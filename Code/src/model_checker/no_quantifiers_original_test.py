from z3 import *
import time

x = BitVec('x_dummy', 3) # basic sort
y = BitVec('y_dummy', 3) # basic sort
z = BitVec('z_dummy', 3) # basic sort
func = Function('func', BitVecSort(3), BoolSort()) # some function
bifunc = Function('bifunc', BitVecSort(3), BitVecSort(3), BoolSort())
trifunc = Function('trifunc', BitVecSort(3), BitVecSort(3), BitVecSort(3), BoolSort())
# ForAll(x, Implies(x==1,func(x))) # existing constraint

def ForAll_iter(bvs, formula, exec_str=None):
    '''
    if exec and eval give trouble, just use the .replace method, which also worked
    '''
    if exec_str:
        exec(exec_str)
    cons_list = []
    formula = str(formula) if not isinstance(formula, str) else formula # make formula a str
    current_bv = bvs if not isinstance(bvs, list) else bvs[0]
    temp_N = current_bv.size()
    num_bvs = 2 ** temp_N
    bv_str = str(current_bv)
    if (not isinstance(bvs, list)) or (isinstance(bvs, list) and len(bvs) == 1):
        for i in range(num_bvs):
            exec(f'{bv_str} = BitVecVal({i},{temp_N})')
            cons_list.append(eval(formula))
        return And(cons_list)
    # recursive call
    rem_bvs = bvs[1:]
    for i in range(num_bvs):
        exec_str = exec_str + f'\n{bv_str} = BitVecVal({i},{temp_N})' if exec_str else f'{bv_str} = BitVecVal({i},{temp_N})'
        cons_list.append(ForAll_iter(rem_bvs, formula, exec_str = exec_str))
    return And(cons_list)


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


