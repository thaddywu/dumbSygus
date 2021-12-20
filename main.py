from re import S
import sys
from typing import AnyStr

from z3.z3 import Map, TreeOrder
import math
import sexp
import copy
import pprint
import translator

limit = 0
all_valid_terms = []
adopted_terms = []
counter_examples = []
last_counter_example = None
last_terms = []
argList = []
Constraints = []
SynFunExpr = []

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
        ret = None
        try:
            if mnemonic == "ite": ret =  evaluate(stmts[2], args, SynFunExpr, synfun) if evaluate(stmts[1], args, SynFunExpr, synfun) else evaluate(stmts[3], args, SynFunExpr, synfun)
            elif mnemonic == "<": ret =  (evaluate(stmts[1], args, SynFunExpr, synfun) < evaluate(stmts[2], args, SynFunExpr, synfun))
            elif mnemonic == "<=": ret =  (evaluate(stmts[1], args, SynFunExpr, synfun) <= evaluate(stmts[2], args, SynFunExpr, synfun))
            elif mnemonic == "=": ret =  (evaluate(stmts[1], args, SynFunExpr, synfun) == evaluate(stmts[2], args, SynFunExpr, synfun))
            elif mnemonic == ">": ret =  (evaluate(stmts[1], args, SynFunExpr, synfun) > evaluate(stmts[2], args, SynFunExpr, synfun))
            elif mnemonic == ">=": ret =  (evaluate(stmts[1], args, SynFunExpr, synfun) >= evaluate(stmts[2], args, SynFunExpr, synfun))
            elif mnemonic == "and": ret =  (evaluate(stmts[1], args, SynFunExpr, synfun) and evaluate(stmts[2], args, SynFunExpr, synfun))
            elif mnemonic == "or": ret =  (evaluate(stmts[1], args, SynFunExpr, synfun) or evaluate(stmts[2], args, SynFunExpr, synfun))
            elif mnemonic == "not": ret =  (not evaluate(stmts[1], args))
            elif mnemonic == "+": ret =  (evaluate(stmts[1], args, SynFunExpr, synfun) + evaluate(stmts[2], args, SynFunExpr, synfun))
            elif mnemonic == "-": ret =  (evaluate(stmts[1], args, SynFunExpr, synfun) - evaluate(stmts[2], args, SynFunExpr, synfun))
            elif mnemonic == "*": ret =  (evaluate(stmts[1], args, SynFunExpr, synfun) * evaluate(stmts[2], args, SynFunExpr, synfun))
            elif mnemonic == "mod": 
                dd = evaluate(stmts[2], args, SynFunExpr, synfun)
                if dd != 0:
                    ret =  evaluate(stmts[1], args, SynFunExpr, synfun) % dd
                else:
                    ret = None
            elif mnemonic == "shr1": ret =  (evaluate(stmts[1], args, SynFunExpr, synfun) >> 1)
            elif mnemonic == "shr4": ret =  (evaluate(stmts[1], args, SynFunExpr, synfun) >> 4)
            elif mnemonic == "shr16": ret =  (evaluate(stmts[1], args, SynFunExpr, synfun) >> 16)
            elif mnemonic == "shl1": ret =  (evaluate(stmts[1], args, SynFunExpr, synfun) << 1) % 18446744073709551616
            elif mnemonic == "bvadd": ret =  (evaluate(stmts[1], args, SynFunExpr, synfun) + evaluate(stmts[2], args, SynFunExpr, synfun)) % 18446744073709551616
            elif mnemonic == "bvand": ret =  (evaluate(stmts[1], args, SynFunExpr, synfun) & evaluate(stmts[2], args, SynFunExpr, synfun))
            elif mnemonic == "bvor": ret =  (evaluate(stmts[1], args, SynFunExpr, synfun) | evaluate(stmts[2], args, SynFunExpr, synfun))
            elif mnemonic == "bvxor": ret =  (evaluate(stmts[1], args, SynFunExpr, synfun) ^ evaluate(stmts[2], args, SynFunExpr, synfun))
            elif mnemonic == "bvnot": ret =  (evaluate(stmts[1], args, SynFunExpr, synfun) ^ 18446744073709551615)
            elif mnemonic == "ite": ret =  evaluate(stmts[2], args, SynFunExpr, synfun) if evaluate(stmts[1], args, SynFunExpr, synfun) == 1 else evaluate(stmts[3], args, SynFunExpr, synfun)
            elif mnemonic == "=>": ret =  (not evaluate(stmts[1], args, SynFunExpr, synfun)) or (evaluate(stmts[2], args, SynFunExpr, synfun))
            elif len(stmts) == 1: ret =  evaluate(stmts[0], args, SynFunExpr, synfun)
            elif SynFunExpr != None and mnemonic == SynFunExpr[1]:
                new_args = {}
                for idx in range(len(SynFunExpr[2])):
                    new_args[SynFunExpr[2][idx][0]] = evaluate(stmts[idx+1], args, SynFunExpr, synfun)
                ret =  evaluate(synfun, new_args, SynFunExpr, synfun)
            else: assert(False)
        except AssertionError:
            assert(False)
        except:
            ret = None
        return ret

def pass_last_example(prog, example, Constraints, SynFunExpr):
    if example == None:
        return True
    # print(prog, example)
    for constr in Constraints:
        # print("----")
        res = evaluate(constr[1:], example, SynFunExpr, prog)
        if res == False or res == None:
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
        declareList = [['placeholderxx', 'Int']]
        for i in range(0, tot1):
            tmpexpr = copy.deepcopy(MappingFrom[i])
            tmpexpr[0] = 'foo%s' % args[i]
            condExpr = ['and', condExpr, ['=', 'tmp%s' % i, tmpexpr]]
            declareList.append(['tmp%s' % i, 'Int'])
        condExpr = ['exists', declareList, condExpr]
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
    # pprint.pprint(newExpr)
    newExpr = newExpr[:-1]
    newExpr.append(['check-sat'])
    new_checker = translator.ReadQuery2(newExpr)
    
    counterexample = new_checker.check()
    # pprint.pprint(newExpr)
    # print(adopted_terms)
    # print(counterexample)
    if (counterexample == None):
        return True, None
        
    for var in ret:
        tmpvar = translator.DeclareVar(ret[var][2], var)
        if counterexample[tmpvar] == None:
            ret[var] = 0
        else:
            ret[var] = counterexample[tmpvar].as_long()
        # print(type(ret[var]))
    
    argcnt = 0
    for expr in bmExpr:
        if len(expr) == 0:
            continue
        elif expr[0] == 'declare-var':
            ret[argcnt] = expr[1]
            argcnt += 1
    # print(ret)
    # print(type(ret))
    return False, ret

def runtest(prog, testcases):
    result = []
    for tc in testcases:
        result.append(int(pass_last_example(prog, tc, Constraints, SynFunExpr)))
    return result

def togroup(prog, testcases):
    # devide testcases
    ret = []
    for tc in testcases:
        args = {}
        for i in range(len(argList)):
            args[argList[i]] = tc[tc[i]]
        output = evaluate(prog, args, None, None)
        ret.append(int(output == 1))
    return ret

def select(terms, TC):
    if len(TC) == 0: return []
    best, sc = terms[0], sum(runtest(terms[0], TC))
    for i in range(1, len(terms)):
        sci = sum(runtest(terms[i], TC))
        if sci > sc:
            sc, best = sci, terms[i]
    
    cover = runtest(best, TC)
    TC0 = []
    for i in range(len(TC)):
        if not cover[i]: TC0.append(TC[i])
    
    return select(terms, TC0) + [best]

def simplifyTerm(terms, testcases):
    ret, meets = [], []
    for term in terms:
        meet = runtest(term, testcases)
        if sum(meet) > 0:
            ret.append(term)
            meets.append(meet)
    return ret, meets

def decisionTree(terms, decisions, testcases):
    # print("DecisionTree", len(terms), len(decisions), len(testcases))
    terms, meets = simplifyTerm(terms, testcases)

    for i in range(len(terms)):
        if sum(meets[i]) == len(testcases):
            #print("[Return]DecisionTree", len(terms), len(decisions), len(testcases))
            #print(terms[i])
            return terms[i]
    
    def entropy(x, y):
        if (x == 0 or y == 0): return 0
        r = 1.0 * x / (x + y)
        return -(r * math.log(r) + (1 - r) * math.log(1 - r))

    def decision_score(dc, debug=False):
        tgs = togroup(dc, testcases)
        score = 0.0
        for i in range(len(terms)):
            cm = [[0, 0], [0, 0]]
            for j in range(len(testcases)):
                cm[tgs[j]][meets[i][j]] += 1
            trueBranch = cm[1][0] + cm[1][1]
            falseBranch = cm[0][0] + cm[0][1]
            tr = trueBranch / (trueBranch + falseBranch)
            fr = falseBranch / (trueBranch + falseBranch)
            score += entropy(cm[0][0] + cm[1][0], cm[0][1] + cm[1][1]) - \
                fr * entropy(cm[0][0], cm[0][1]) - tr * entropy(cm[1][0], cm[1][1])
            if (debug): print(cm)
        return score
    
    best, ds = 0, decision_score(decisions[0])
    for i in range(1, len(decisions)):
        dsi = decision_score(decisions[i])
        if dsi > ds:
            ds, best = dsi, i
    
    trueTestCases = []
    falseTestCases = []
    tgs = togroup(decisions[best], testcases)
    for i in range(len(testcases)):
        if tgs[i]: trueTestCases.append(testcases[i])
        else: falseTestCases.append(testcases[i])

    '''
    print("=================== Meet ================")
    for meet in meets:
        print(meet)
    print("=================== decisions ================")
    for i in range(0, len(decisions)):
        print(togroup(decisions[i], testcases))
    '''
    #print(meets)
    # #x=str(input())

    trueBranch = decisionTree(terms, decisions, trueTestCases)
    falseBranch = decisionTree(terms, decisions, falseTestCases)
    
    ret = ['ite', decisions[best], trueBranch, falseBranch]
    #print("[Return]DecisionTree", len(terms), len(decisions), len(testcases))
    #print(ret)
    return ret

def generate_new_terms():
    global limit
    global last_terms
    global all_valid_terms
    global adopted_terms
    global counter_examples
    global last_counter_example

    if limit > 5:
        return False 

    limit += 1
    now_terms = searchTerm(last_terms, Productions)
    last_terms = now_terms
    for term in now_terms:
        if fullStmt(term, Productions):
            all_valid_terms.append(term)

    return True

def ExtendBool(Stmts,Productions,Type):
    ret = []
    for i in range(len(Stmts)):
        if type(Stmts[i]) == list:
            TryExtend = ExtendBool(Stmts[i],Productions, Type)
            if TryExtend == None:
                return None
            if len(TryExtend) > 0 :
                for extended in TryExtend:
                    ret.append(Stmts[0:i]+[extended]+Stmts[i+1:])
                return ret
        elif type(Stmts[i]) == tuple:
            continue
        elif Stmts[i] in Productions:
            if Type[Stmts[i]] == 'Bool':
                for extended in Productions[Stmts[i]]:
                    # remove ite in simple terms
                    if type(extended) == list and extended[0] == 'and':
                        continue
                    ret.append(Stmts[0:i]+[extended]+Stmts[i+1:])
                return ret
            else:
                for term in all_valid_terms:
                    ret.append(Stmts[0:i]+term+Stmts[i+1:])
                return ret
    return ret

def searchBoolTerm(InitList, Productions, Type):
    TE_set = set()
    ret = []
    for Curr in InitList:
        TryExtend = ExtendBool(Curr, Productions, Type)
        if TryExtend == None:
            continue
        for TE in TryExtend:
            TE_str = str(TE)
            if not TE_str in TE_set:
                TE_set.add(TE_str)
                ret.append(TE)

    return ret

def generate_bool_expressions(bmExpr, Productions, size_limit, Type):
    ret = []
    last_bool_terms = []
    now_bool_terms = []
    for nonterm in Productions:
        if Type[nonterm] == 'Bool':
            last_bool_terms.append([nonterm])
    for _ in range(size_limit):
        now_bool_terms = searchBoolTerm(last_bool_terms, Productions, Type)
        last_bool_terms = now_bool_terms
        for term in now_bool_terms:
            if fullStmt(term, Productions):
                ret.append(term)
    
    return ret
             
def decide_and_verify(SynFunExpr, Productions, bmExpr, Type):
    terms = select(all_valid_terms, counter_examples)
    meets = [runtest(term, counter_examples) for term in terms]
    def complete(conditions):
        tn = len(counter_examples)
        equi = [-1 for i in range(tn)]
        results = [togroup(prog, counter_examples) for prog in conditions]

        def equivalent(i, j):
            # return wheter test #i and test #j is equivalent
            for k in range(len(conditions)):
                if results[k][i] != results[k][j]: return False
            return True
        
        def allcover(eqclass):
            # return whether some term could cover all tests in eqclass
            for i in range(len(terms)):
                meetall = True
                for j in eqclass:
                    if not meets[i][j]: meetall = False
                if meetall: return True
            return False

        for i in range(tn):
            if equi[i] != -1: continue
            equi[i] = i
            eqclass = [i]
            for j in range(i + 1, tn):
                if not equivalent(i, j): continue
                equi[j] = i
                eqclass.append(j)
                # Can't distinguish test #i, i in eq_class
            if not allcover(eqclass): return False
        
        return True
                
        # equivalent tests

    # search conditions
    conditions = []
    while True:
        conditions = generate_bool_expressions(bmExpr, Productions, 5, Type)
        if complete(conditions): break
        if not generate_new_terms():
            assert False

    prog = decisionTree(terms, conditions, counter_examples)
    progToken = translator.toString(prog)
    FuncDefineStr = translator.toString(FuncDefine,ForceBracket = True)
    ans = FuncDefineStr[:-1] + " " + progToken + FuncDefineStr[-1]
    # print(ans)
    return ans

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

    for arg in SynFunExpr[2]:
        argList.append(arg[0])

    last_terms = [[StartSym]]
    added_terms = set()

    while True and limit <= 10:
        print("hello", limit, counter_examples, len(all_valid_terms))
        flag = False
        for term in all_valid_terms:
            if pass_last_example(term, last_counter_example, Constraints, SynFunExpr):
                flag = True
                # print("pass:",adopted_terms)
                adopted_terms.append(term)
                if not (str(term) in added_terms):
                    added_terms.add(str(term))
                break
        if flag:
            result, emp = check_equiv(adopted_terms, bmExpr, SynFunExpr)
            if result:
                prog = decide_and_verify(SynFunExpr, Productions, bmExpr, Type)
                cemp = checker.check(prog)
                if (cemp == None):
                    print(prog)
                    break
                else:
                    res = {}
                    for expr in bmExpr:
                        if len(expr) == 0:
                            continue
                        elif expr[0] == 'declare-var':    
                            res[expr[1]] = expr
                    for var in res:
                        tmpvar = translator.DeclareVar(res[var][2], var)
                        if cemp[tmpvar] == None:
                            res[var] = 0
                        else:
                            res[var] = cemp[tmpvar].as_long()
                    argcnt = 0
                    for expr in bmExpr:
                        if len(expr) == 0:
                            continue
                        elif expr[0] == 'declare-var':
                            res[argcnt] = expr[1]
                            argcnt += 1
                    counter_examples.append(res)
                    last_counter_example = res
            else:
                counter_examples.append(emp)
                last_counter_example = emp
                pass
        else:
            generate_new_terms()
       

	# Examples of counter-examples    
	# print (checker.check('(define-fun max2 ((x Int) (y Int)) Int 0)'))
    # print (checker.check('(define-fun max2 ((x Int) (y Int)) Int x)'))
    # print (checker.check('(define-fun max2 ((x Int) (y Int)) Int (+ x y))'))
    # print (checker.check('(define-fun max2 ((x Int) (y Int)) Int (ite (<= x y) y x))'))
