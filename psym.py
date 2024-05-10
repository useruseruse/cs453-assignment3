import argparse
import importlib
import sys
from z3 import *


### find the parameter of function and make it as proxy value !!!
path=[]
pathcondition = []
path_solutions = []    
test_sets = []    


# 1. Implement peer lightweight symbolic execution engine
class IntProxy:
    def __init__(self, term):
        self.term = term  # term is expected to be a Z3 expression or variable

    def __add__(self, other):
        if type(other) == int:
            other = IntProxy(other)
        return IntProxy(self.term + other.term)

    def __radd__(self, other):
        return self.__add__(other)
    
    def __sub__(self, other):  # "-" 연산자에 대해서 정의함
        if type(other) == int:
            other = IntProxy(other)
        return IntProxy(self.term - other.term)

    def __rsub__(self, other):
        return self.__sub__(other)
    
    def __mod__(self, other): # "%" 연산자에 대해서 정의함
        if type(other) == int:
            other = IntProxy(other)
        return IntProxy(self.term % other.term)

    def __rmod__(self, other):
        return self.__mod__(other)
    
    def __pow__(self, exponent):  # "**" 연산자에 대해서 정의함
        if type(exponent) == int:
            exponent = IntProxy(exponent)
        return IntProxy(self.term ** exponent.term)
    
    def __rpow__(self, other):
        return self.__pow__(other)

    def __neg__(self):  # "- value" 연산자에 대해서 정의함
        return IntProxy(-self.term)
    
    def __mul__(self, other):
        if type(other) == int:
            other = IntProxy(other)
        return IntProxy(self.term * other.term)

    def __rmul__(self, other):
        return self.__mul__(other)
    #-------------------- 비교 연산자에 대해서 정의함. --------------------

    def __eq__(self, other):
        if type(other) == int:
            other = IntProxy(other)
        return BoolProxy(self.term == other.term)

    def __req__(self, other):
        # Reverse the equality operation, it's commutative
        return self.__eq__(other)
    
    def __lt__(self, other):
        if type(other) == int:
            other = IntProxy(other)
        return BoolProxy(self.term < other.term)
    
    def __le__(self, other):
        if type(other) == int:
            other = IntProxy(other)
        return BoolProxy(self.term <= other.term)
    
    def __gt__(self, other):
        if type(other) == int:
            other = IntProxy(other)
        return BoolProxy(self.term > other.term)
    
    def __ge__(self, other):
        if type(other) == int:
            other = IntProxy(other)
        return BoolProxy(self.term >= other.term)

    def __ne__(self, other):
        if type(other) == int:
            other = IntProxy(other)
        return BoolProxy(self.term != other.term)
    
    def __and__(self, other):
        if type(other) == int:
            other = IntProxy(other)
        return BoolProxy(And(self.term, other.term))
    
    def __or__(self, other):
        if type(other) == int:
            other = IntProxy(other)
        return BoolProxy(Or(self.term, other.term))


class BoolProxy(object):
    def __init__(self, formula):
        self.formula = formula

    def __not__(self):
        return Bool(Not(self.formula))

    def __bool__(self):
        global path, pathcondition, path_solutions
        solver = Solver()

        # Check if the true and the false branches can be selected
        solver.add(*pathcondition, self.formula)
        true_cond = (solver.check() == sat)

        solver.reset()
        solver.add(*pathcondition, Not(self.formula))
        false_cond = (solver.check() == sat)

        if true_cond and not false_cond:   return True
        elif false_cond and not true_cond: return False
        
        if len(path) > len(pathcondition):
            branch = path[len(pathcondition)]      # branch 가 true 면, 아직 true/false 모두 탐색을 안한 것..
            pathcondition.append(self.formula if branch else Not(self.formula))
            return branch
        
        if len(path) >= 15: raise Exception("Depth Exception")
    
        path.append(True)
        pathcondition.append(self.formula)
        return True

## get_solution 함수는 pathcondition 을 받아서, 해당 pathcondition 을 만족하는 해를 찾아서 리턴함
def get_solution(pathcondition):
    solver = Solver()
    solver.add(*pathcondition)
    if solver.check() == sat:
        return solver.model()
    return None

def get_model_str(model, params):   
    model_string_list = []
    for d in model.decls():
        model_string_list.append(f"{d.name()} = {model[d]}")
        params.remove(d.name())
    
    # 만약 path condition 과 무관한 param 이 ㅇ
    while params:
        model_string_list.append(f"{params.pop()} = 0")
    return model_string_list    

def test(f, *args, **kwargs):
    global path, pathcondition
    test_sets = []
    path = []
    while True:
        pathcondition = []
        try:
            result = f(*args, **kwargs)
        except Exception as e:
            print(e)
                
        model = get_solution(pathcondition)  ## path condition 을 만족하는 해를 구합니다. 
        model_string_list = get_model_str(model, get_function_parameters(f))  ## 해당 해를 string 으로 변환합니다.
        test_sets.append(model_string_list)
       
        # 1. Remove all False branch points since they have been totally explored
        while len(path) > 0 and not path[-1]:
            path.pop()

        # 2. If path is empty the whole branch tree has been explored
        # 탐색이 끝나면, 찾은 test case (test input들의 집합)을 반환함. 
        if not path:
            return test_sets 
        
        # 3. Switch the last true branch to false to explore the other path
        path[-1] = False


import inspect

def get_function_parameters(func):
    sig = inspect.signature(func)
    return [param.name for param in sig.parameters.values()]

# 함수의 parameter들에 대해서 Int Proxy 를 생성한뒤, test 를  실행함
def symbolic_execute(func):
    params = get_function_parameters(func)     
    proxies = {name: IntProxy(Int(name)) for name in params}
    test_sets = test(func, *proxies.values())  
    return test_sets


def execute_all_functions(module):
    test_map = {}   
    for attr_name, attr in inspect.getmembers(module, inspect.isfunction) :
        if callable(attr) and not attr_name.startswith('__'): ## test file 내에 있는 모든 함수들에 대해서 symbolic execution 을 실행함 (private 함수들을 제외하고..)
            # Exclude built-in functions and methods
            if inspect.isfunction(attr):
                print(f"Executing {attr_name}")  
                try:
                    test_sets = symbolic_execute(attr)  ## 해당 함수에 대해서 symbolic execute 실행 
                    test_map[attr_name] = test_sets
                    print(f"Tests for {attr_name}: {test_sets}")
                except Exception as e:
                    print(f"Error executing {attr_name}: {e}")
    return test_map


if __name__ == '__main__':
    parser = argparse.ArgumentParser(description='Symbolically execute all functions in a specified file.')
    parser.add_argument('-t', '--target', required=True, help="the target file to symbolically execute")
    # sys.argv = ['examples/example1.py']
    # module_name = sys.argv[0]

    args = parser.parse_args()
    module_name = args.target

    spec = importlib.util.spec_from_file_location("module.name", module_name)
    module = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(module)

    # Execute all functions within the module
    test_map = execute_all_functions(module)


    # 3. Generate PyTest unit test cases
    test_cases = []
    idx = 0

    directory = os.path.dirname(args.target)
    test_filename = f"test_{os.path.basename(args.target)}"
    test_file_path = os.path.join(directory, test_filename)
    
    for func_name in test_map.keys():
        for inputs in test_map[func_name]:
            # for input in inputs:
            test_cases.append(
            """\ndef test_case_{}(): \n  {}({})""".format(idx, func_name, ','.join(inputs)))
            idx += 1

    # Writing test cases to a Python test file
    file = 'test_' + module_name.split('/')[1]
    with open('{}'.format(test_file_path), 'w') as f:
        f.write("import pytest\n")
        f.write("from {} import *\n ".format(module_name.split('.')[0].split('/')[1]))
        f.writelines(test_cases)
   