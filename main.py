from re import S
import sys
from typing import AnyStr

from z3.z3 import Map
import sexp
import copy
import pprint
import translator

def fullStmt(Stmt, Productions):
    for i in range(len(Stmt)):
        if type(Stmt[i]) == tuple:
            continue
        elif type(Stmt[i]) == list:
            if fullStmt(Stmt[i], Productions):
                continue
            else:
                return False
        elif Stmt[i] in Productions:
            return False
    return True

def Extend(Stmts,Productions):
    ret = []
    for i in range(len(Stmts)):
        if type(Stmts[i]) == list:
            TryExtend = Extend(Stmts[i],Productions)
            if TryExtend == None:
                return None
            if len(TryExtend) > 0 :
                for extended in TryExtend:
                    ret.append(Stmts[0:i]+[extended]+Stmts[i+1:])
                return ret
        elif type(Stmts[i]) == tuple:
            continue
        elif Stmts[i] in Productions:
            for extended in Productions[Stmts[i]]:
                # remove ite in simple terms
                if type(extended) == list and extended[0] == 'ite':
                    continue
                ret.append(Stmts[0:i]+[extended]+Stmts[i+1:])
            return ret
    return ret

def stripComments(bmFile):
    noComments = '(\n'
    for line in bmFile:
        line = line.split(';', 1)[0]
        noComments += line
    return noComments + '\n)'

def searchTerm(InitList, Productions):
    TE_set = set()
    ret = []
    for Curr in InitList:
        TryExtend = Extend(Curr, Productions)
        if TryExtend == None:
            continue
        for TE in TryExtend:
            TE_str = str(TE)
            if not TE_str in TE_set:
                TE_set.add(TE_str)
                ret.append(TE)

    return ret

def evaluate(stmts, args, SynFunExpr, synfun):
    # print("TEST!:",stmts, args)
    if type(stmts) != list:
        # print("b1")
        if type(stmts) == tuple: return int(stmts[1])
        return args[stmts] if stmts in args else stmts
    else:
        # print("b2")
        mnemonic = stmts[0]
        if mnemonic == "ite": return evaluate(stmts[2], args, SynFunExpr, synfun) if evaluate(stmts[1], args, SynFunExpr, synfun) else evaluate(stmts[3], args, SynFunExpr, synfun)
        elif mnemonic == "<": return (evaluate(stmts[1], args, SynFunExpr, synfun) < evaluate(stmts[2], args, SynFunExpr, synfun))
        elif mnemonic == "<=": return (evaluate(stmts[1], args, SynFunExpr, synfun) <= evaluate(stmts[2], args, SynFunExpr, synfun))
        elif mnemonic == "=": return (evaluate(stmts[1], args, SynFunExpr, synfun) == evaluate(stmts[2], args, SynFunExpr, synfun))
        elif mnemonic == ">": return (evaluate(stmts[1], args, SynFunExpr, synfun) > evaluate(stmts[2], args, SynFunExpr, synfun))
        elif mnemonic == ">=": return (evaluate(stmts[1], args, SynFunExpr, synfun) >= evaluate(stmts[2], args, SynFunExpr, synfun))
        elif mnemonic == "and": return (evaluate(stmts[1], args, SynFunExpr, synfun) and evaluate(stmts[2], args, SynFunExpr, synfun))
        elif mnemonic == "or": return (evaluate(stmts[1], args, SynFunExpr, synfun) or evaluate(stmts[2], args, SynFunExpr, synfun))
        elif mnemonic == "not": return (not evaluate(stmts[1], args))
        elif mnemonic == "+": return (evaluate(stmts[1], args, SynFunExpr, synfun) + evaluate(stmts[2], args, SynFunExpr, synfun))
        elif mnemonic == "-": return (evaluate(stmts[1], args, SynFunExpr, synfun) - evaluate(stmts[2], args, SynFunExpr, synfun))
        elif mnemonic == "*": return (evaluate(stmts[1], args, SynFunExpr, synfun) * evaluate(stmts[2], args, SynFunExpr, synfun))
        elif mnemonic == "mod": return (evaluate(stmts[1], args, SynFunExpr, synfun) % evaluate(stmts[2], args, SynFunExpr, synfun))
        elif mnemonic == "shr1": return (evaluate(stmts[1], args, SynFunExpr, synfun) >> 1)
        elif mnemonic == "shr4": return (evaluate(stmts[1], args, SynFunExpr, synfun) >> 4)
        elif mnemonic == "shr16": return (evaluate(stmts[1], args, SynFunExpr, synfun) >> 16)
        elif mnemonic == "shl1": return (evaluate(stmts[1], args, SynFunExpr, synfun) << 1) % 18446744073709551616
        elif mnemonic == "bvadd": return (evaluate(stmts[1], args, SynFunExpr, synfun) + evaluate(stmts[2], args, SynFunExpr, synfun)) % 18446744073709551616
        elif mnemonic == "bvand": return (evaluate(stmts[1], args, SynFunExpr, synfun) & evaluate(stmts[2], args, SynFunExpr, synfun))
        elif mnemonic == "bvor": return (evaluate(stmts[1], args, SynFunExpr, synfun) | evaluate(stmts[2], args, SynFunExpr, synfun))
        elif mnemonic == "bvxor": return (evaluate(stmts[1], args, SynFunExpr, synfun) ^ evaluate(stmts[2], args, SynFunExpr, synfun))
        elif mnemonic == "bvnot": return (evaluate(stmts[1], args, SynFunExpr, synfun) ^ 18446744073709551615)
        elif mnemonic == "if0": return evaluate(stmts[2], args, SynFunExpr, synfun) if evaluate(stmts[1], args, SynFunExpr, synfun) == 1 else evaluate(stmts[3], args, SynFunExpr, synfun)
        elif len(stmts) == 1: return evaluate(stmts[0], args, SynFunExpr, synfun)
        elif mnemonic == SynFunExpr[1]:
            new_args = {}
            for idx in range(len(SynFunExpr[2])):
                new_args[SynFunExpr[2][idx][0]] = evaluate(stmts[idx+1], args, SynFunExpr, synfun)
            return evaluate(synfun, new_args, SynFunExpr, synfun)
        else: assert(False)

def pass_last_example(prog, example, Constraints, SynFunExpr):
    if example == None:
        return True
    # print(prog, example)
    for constr in Constraints:
        # print("----")
        if evaluate(constr[1:], example, SynFunExpr, prog) == False:
            return False
    return True

def replaceExpr(term, args, MappingTo):
    for i in range(len(term)):
        if type(term[i]) == list:
            if str(term[i]) in MappingTo:
                term[i][0] = "foo%s" % args[MappingTo[str(term[i])]]
            replaceExpr(term[i], args, MappingTo)

def add_mapping(term, MappingTo, MappingFrom, SynFunExpr):
    for i in range(len(term)):
        if type(term[i]) == list:
            if term[i][0] == SynFunExpr[1]:
                if not (str(term[i]) in MappingTo):
                    MappingTo[str(term[i])]=len(MappingTo)
                    MappingFrom[MappingTo[str(term[i])]] = term[i]
            add_mapping(term[i], MappingTo, MappingFrom, SynFunExpr)

def generate_mapping(Constraints, MappingTo, MappingFrom, SynFunExpr):
    for expr in Constraints:
        add_mapping(expr[1:], MappingTo, MappingFrom, SynFunExpr)

def recursive_add(pos, tot1, tot2, newExpr, Constraints, MappingTo, MappingFrom, args):
    if pos == tot1:
        condExpr = 'true'
        for constr in Constraints:
            tmpexpr = copy.deepcopy(constr[1:])
            replaceExpr(tmpexpr, args, MappingTo)
            condExpr = ['and', condExpr, tmpexpr]
        for i in range(0, tot1):
            tmpexpr = copy.deepcopy(MappingFrom[i])
            tmpexpr[0] = 'foo%s' % args[i]
            condExpr = ['and', condExpr, ['=', 'tmp%s' % i, tmpexpr]]
            condExpr = ['exists', [['tmp%s' % i, 'Int']], condExpr]
        # TODO: Missing some equalities
        newExpr.insert(-1,['constraint', 'not', condExpr])        
        return

    for i in range(tot2):
        args[pos] = i
        recursive_add(pos+1, tot1, tot2, newExpr, Constraints, MappingTo, MappingFrom, args)

def check_equiv(adopted_terms, bmExpr, SynFunExpr):
    newExpr = []
    Constraints = []
    ret = {}
    for expr in bmExpr:
        if len(expr) == 0:
            continue
        elif expr[0] == 'synth-fun':
            continue
        elif expr[0] == 'constraint':
            Constraints.append(expr)
        else:
            if expr[0] == 'declare-var':
                ret[expr[1]] = expr
            newExpr.append(expr)

    MappingTo = {}
    MappingFrom = {}
    generate_mapping(Constraints, MappingTo, MappingFrom, SynFunExpr)

    # for i in range(len(MappingTo)):
    #     newExpr.insert(-1,['declare-var', 'tmp%s' % str(i),'Int'])

    for i in range(len(adopted_terms)):
        newExpr.insert(-1,['define-fun', 'foo%s' % str(i)]+SynFunExpr[2:4]+adopted_terms[i])

    recursive_add(0, len(MappingTo), len(adopted_terms), newExpr, Constraints, MappingTo, MappingFrom, {})
    pprint.pprint(newExpr)
    newExpr = newExpr[:-1]
    newExpr.append(['check-sat'])
    new_checker = translator.ReadQuery2(newExpr)
    
    counterexample = new_checker.check()
    pprint.pprint(newExpr)
    print(adopted_terms)
    print(counterexample)
    if (counterexample == None):
        return True, None
        
    for var in ret:
        tmpvar = translator.DeclareVar(ret[var][2], var)
        ret[var] = counterexample[tmpvar].as_long()
        # print(type(ret[var]))
    # print(ret)
    # print(type(ret))
    return False, ret
             
def decide_and_verify(adopted_terms, counter_examples, SynFunExpr):
    assert False

if __name__ == '__main__':
    benchmarkFile = open(sys.argv[1])
    bm = stripComments(benchmarkFile)
    bmExpr = sexp.sexp.parseString(bm, parseAll=True).asList()[0]
    # pprint.pprint(bmExpr)
    checker=translator.ReadQuery(bmExpr)
    SynFunExpr = []
    StartSym = 'My-Start-Symbol'
    Constraints = []
    for expr in bmExpr:
        if len(expr)==0:
            continue
        elif expr[0]=='synth-fun':
            SynFunExpr=expr
        elif expr[0]=='constraint':
            Constraints.append(expr)
    FuncDefine = ['define-fun']+SynFunExpr[1:4]
    Productions = {StartSym:[]}
    Type = {StartSym:SynFunExpr[3]}
    for NonTerm in SynFunExpr[4]:
        NTName = NonTerm[0]
        NTType = NonTerm[1]
        if NTType == Type[StartSym]:
            Productions[StartSym].append(NTName)
        Type[NTName] = NTType
        Productions[NTName] = NonTerm[2]

    all_valid_terms = []
    last_terms = [[StartSym]]
    adopted_terms = []
    counter_examples = []
    last_counter_example = None
    limit = 0
    while True and limit <= 5:
        print("hello", limit, counter_examples, len(all_valid_terms))
        flag = False
        for term in all_valid_terms:
            if pass_last_example(term, last_counter_example, Constraints, SynFunExpr):
                flag = True
                print("pass:",term)
                adopted_terms.append(term)
                break
        if flag:
            result, emp = check_equiv(adopted_terms, bmExpr, SynFunExpr)
            if result:
                if decide_and_verify(adopted_terms, counter_examples, SynFunExpr):
                    break
                else:
                    last_counter_example = counter_examples[-1]
            else:
                counter_examples.append(emp)
                last_counter_example = emp
                pass
        else:
            limit += 1
            now_terms = searchTerm(last_terms, Productions)
            last_terms = now_terms
            for term in now_terms:
                if fullStmt(term, Productions):
                    all_valid_terms.append(term)
       

	# Examples of counter-examples    
	# print (checker.check('(define-fun max2 ((x Int) (y Int)) Int 0)'))
    # print (checker.check('(define-fun max2 ((x Int) (y Int)) Int x)'))
    # print (checker.check('(define-fun max2 ((x Int) (y Int)) Int (+ x y))'))
    # print (checker.check('(define-fun max2 ((x Int) (y Int)) Int (ite (<= x y) y x))'))
