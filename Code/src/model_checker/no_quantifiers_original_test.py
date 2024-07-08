from z3 import *
import time
import random

x = BitVec('x', 3) # basic sort
y = BitVec('y', 3) # basic sort
z = BitVec('z', 3) # basic sort
func = Function('func', BitVecSort(3), BoolSort()) # some function
bifunc = Function('bifunc', BitVecSort(3), BitVecSort(3), BoolSort())
trifunc = Function('trifunc', BitVecSort(3), BitVecSort(3), BitVecSort(3), BoolSort())
# ForAll(x, Implies(x==1,func(x))) # existing constraint


def find_rest_and_old_name(formula_fragment):
    '''
    formula_fragment is a str and starts AFTER the parenthesis after Exists
    returns a tuple of the rest of the formula and the old bv name
    '''
    old_bv_name = ''
    for i, char in enumerate(formula_fragment):
        if char == ',':
            return formula_fragment[i+2:-1], old_bv_name # remove ')'
        if char == '\t' or char == '\n': # dunno if necessary
            continue
        old_bv_name += char

def remove_Exists_in_univ_scope(formula):
    '''
    formula is a str
    returns tuple of new formula and old bv name that was the bound variable
    '''
    new_formula = ''
    for i, char in enumerate(formula):
        if formula[i:i+6] == 'Exists':
            rest_of_formula, old_bv_name = find_rest_and_old_name(formula[i+7:])
            new_formula += rest_of_formula
            return new_formula, old_bv_name
        new_formula += char


def ForAll_iter(bvs, formula, exec_str=None):
    '''
    if exec and eval give trouble, just use the .replace method, which also worked
    '''
    if exec_str:
        exec(exec_str)
    cons_list = []
    # formula = str(formula) if not isinstance(formula, str) else formula # make formula a str
    current_bv = bvs if not isinstance(bvs, list) else bvs[0]
    temp_N = current_bv.size()
    num_bvs = 2 ** temp_N
    lambda_formula = Lambda(bvs, formula)
    if (not isinstance(bvs, list)) or (isinstance(bvs, list) and len(bvs) == 1):
        for i in range(num_bvs):
            quant_inst = BitVecVal(i,temp_N)
            cons_list.append(lambda_formula[quant_inst])
            # if 'Exists' in formula:
            #     new_formula, old_bbv_name = remove_Exists_in_univ_scope(formula)
            #     new_bbv_name = old_bbv_name+str(i)
            #     exec(f'{new_bbv_name} = BitVec("{new_bbv_name}",{temp_N})')
            #     new_formula = new_formula.replace(old_bbv_name, new_bbv_name)
            # exec(f'{bv_str} = BitVecVal({i},{temp_N})')
            # print(f'vars: {vars()}\n\ndir: {dir()}\n\n\n')
            # cons_list.append(eval(new_formula))
        return And(cons_list)
    # recursive call
    for i in range(num_bvs):
        outer_quant_inst = BitVecVal(i,temp_N)
        new_lambda_formula = lambda_formula[outer_quant_inst]
        print(new_lambda_formula)
        for j in range(num_bvs):
            inner_quant_inst = BitVecVal(j,temp_N)
            final_lambda = new_lambda_formula[inner_quant_inst]
            cons_list.append(final_lambda)
        # exec_str = exec_str + f'\n{bv_str} = BitVecVal({i},{temp_N})' if exec_str else f'{bv_str} = BitVecVal({i},{temp_N})'
        # cons_list.append(ForAll_iter(rem_bvs, formula, exec_str = exec_str))
    return And(cons_list)

######### TESTING UNIVERSAL QUANTIFIER ##########
# test_formula = ForAll(x, And(Implies(x==1,func(x)),Implies(func(x),x==1)))
# test_formula = ForAll([x,y], And(Implies(x==y,bifunc(x,y)),Implies(bifunc(x,y),x==y)))
test_formula = ForAll([x,y,z], And(Implies(x+y==z,trifunc(x,y,z)),Implies(trifunc(x,y,z),x+y==z)))

print('iter')
iter_solver = Solver()
start = time.time()
# result = iter_solver.check(ForAll_iter(x, And(Implies(x==1,func(x)),Implies(func(x),x==1))))
iter_result = iter_solver.check(ForAll_iter([x,y,z], And(Implies(x+y==z,trifunc(x,y,z)),Implies(trifunc(x,y,z),x+y==z))))
print('quant')
quant_solver = Solver()
middle = time.time()
quant_result = quant_solver.check(test_formula)
end = time.time()
if iter_result == sat and quant_result == sat:
    for i in range(2 ** x.size()):
        for j in range(2 ** y.size()):
            for k in range(2 ** z.size()):
                # print(f'{i,j,k}, {iter_solver.model().evaluate(trifunc(i,j,k))}')
                iter_value = iter_solver.model().evaluate(trifunc(i,j,k))
                quant_value = quant_solver.model().evaluate(trifunc(i,j,k))
                if quant_value and not iter_value:
                    print(i,j,k)
                print(f'{i,j,k}, {iter_value == quant_value}')

# print('quant')
# quant_solver = Solver()
# quant_result = quant_solver.check(test_formula)
# end = time.time()
# if result == sat:
#     for i in range(2 ** x.size()):
#         for j in range(2 ** y.size()):
#             for k in range(2 ** z.size()):
#                 print(f'{i,j,k}, {quant_solver.model().evaluate(trifunc(i,j,k))}')
print(f'no quantifiers time: {middle-start}')
print(f'with quantifiers time: {end-middle}')


def Exists_new(bv, formula): # we only ever use a single bv for Exists—no recursive bs!
    # return formula
    formula_str = str(formula)
    temp_N = bv.size()
    bv_str = str(bv)
    # randid = str(random.randint(0,10000))
    # new_bv_str = bv_str + randid
    # exec(f'{new_bv_str} = BitVec("{new_bv_str}",{temp_N})')
    # new_formula_str = formula_str.replace(bv_str, new_bv_str)
    # return eval(new_formula_str)
    exec(f'{bv_str} = BitVec("{bv_str}",{temp_N})')
    return eval(formula_str)

    if 'ForAll' in formula_str:
        pass
    
    return formula
    formula = str(formula) if not isinstance(formula, str) else formula # make formula a str
    temp_N = bv.size()
    bv_str = str(bv)
    exec(f'{bv_str} = BitVec("{bv_str}", {temp_N})')
    return eval(formula)

def test_Exists():
    no_quant_solver = Solver()
    quant_solver = Solver()
    ue = ForAll(y, Exists(x, x+y==0))
    eu = Exists(x, ForAll(y, x+y==0))
    # print(f'ue: {ForAll_iter(y, Exists_new(x, x+y==0))}') # should find a model
    # print(f'eu: {Exists_new(x, ForAll_iter(y, x+y==0))}') # should not find a model
    no_quant_result = no_quant_solver.check(ForAll_iter(y, Exists(x, x+y==0)))
    # solver_tested = no_quant_solver
    # quant_result = quant_solver.check(ue)
    if no_quant_result == sat:
        print('model was found')
    if no_quant_result == unsat:
        print(no_quant_solver.unsat_core())

test_Exists()