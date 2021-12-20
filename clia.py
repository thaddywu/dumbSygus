from re import T
import sys
import sexp
import pprint
import translator
import evaluator
from queue import PriorityQueue
import math
import random

q = PriorityQueue()

testcases = []

argList = []
arg2call = dict()
call2arg = dict()
Productions = {}

callExpr = None
checker = None

def substitute(prog, term):
    if type(prog) != list: return prog
    if prog == callExpr: return term
    return [substitute(item, term) for item in prog]

def inputMatch(tc):
    newc = []
    for arg, value in zip(call2arg.keys(), tc):
        if len(newc) > 0:
            newc = ["and", newc, ["=", arg, ("Int", value)]]
        else:
            newc = ["=", arg, ("Int", value)]
    return newc

def generateValidInputs(TN = 50):
    #for i in range(TN):
    #    testcases.append([random.randint(-100, 100) for j in range(len(argList))])
    #return True

    MagicNumber = ("Int", -19260817)
    
    inputList = None

    for i in range(TN):
        subSpec = substitute(checker.Spec, MagicNumber)
        if inputList is None:
            model = checker.mycheck(["not", subSpec])
        else:
            model = checker.mycheck(["and", ["not", inputList], ["not", subSpec]])
        if model is None: return False # no more input

        tc = resolve(model)
        testcases.append(tc)

        inputList = inputMatch(tc) if inputList is None else ["or", inputList, inputMatch(tc)]
    
    #print(testcases)
    return True


def runtestOne(prog, tc):
    # print("Run test", prog, tc)
    retVar = ("Int", evaluator.evaluate(prog, dict(zip(argList, tc))))
    subSpec = substitute(checker.Spec, retVar)
    # print(subSpec, dict(zip(call2arg.keys(), tc)))
    return checker.mycheck(["and", subSpec, inputMatch(tc)]) is not None

def runtest(prog, TC=testcases):
    result = []
    for tc in TC:
        result.append(runtestOne(prog, tc))
    return result

def getMnemonic(stmts):
    if type(stmts) == list:
        return getMnemonic(stmts[0])
    elif type(stmts) == tuple:
        return getMnemonic(stmts[0])
    return stmts

def Extend(Stmts, Productions, cost):
    ret = []
    for i in range(len(Stmts)):
        if type(Stmts[i]) == list:
            TryExtend = Extend(Stmts[i], Productions, cost)
            if len(TryExtend) > 0:
                for extended in TryExtend:
                    ret.append((extended[0], Stmts[0:i]+[extended[1]]+Stmts[i+1:]))
                return ret
        elif type(Stmts[i]) == tuple:
            continue
        elif Stmts[i] in Productions:
            for extended in Productions[Stmts[i]]:
                ext_cost = evaluator.cost(getMnemonic(extended)) * cost
                ret.append((ext_cost, Stmts[0:i]+[extended]+Stmts[i+1:]))
            return ret
    return ret

def search(thres, intSymbol):
    q = PriorityQueue()
    q2format = {}
    inQueue = set()

    def qadd(cost, prog):
        token = translator.toString(prog)
        if token in inQueue: return 
        q2format[token] = prog
        q.put((cost, token))
        inQueue.add(token)
        
    qadd(1.0, [intSymbol])

    tn = len(testcases)
    cover = [0 for i in range(tn)]
    terms = []
    while not q.empty():
        cost, progToken = q.get()
        prog = q2format[progToken]
        # print(cost, ":", progToken)
        # x=str(input())
        TryExtend = Extend(prog, Productions, cost)
        if len(TryExtend) == 0:
            ans = FuncDefineStr[:-1] + " " + progToken + FuncDefineStr[-1]
            rs = runtest(prog)
            score = sum(rs)
            #if score == tn: return ans, True
            if score > 0:
                for i in range(tn):
                    if rs[i]: cover[i] = 1
                terms += prog
                if sum(cover) == tn: return terms, True
            continue
        
        for ext in TryExtend:
            if ext[0] < thres: qadd(ext[0], ext[1])
    
    # print(cover)
    return None, False

def togroup(prog, testcases):
    # devide testcases
    ret = []
    for tc in testcases:
        output = evaluator.evaluate(prog, dict(zip(argList, tc)))
        ret.append(int(output))
    return ret

def searchDecision(thres, boolSymbol):
    # generate conditions to divide exprs into groups
    q = PriorityQueue()
    q2format = {}
    inQueue = set()

    def qadd(cost, prog):
        token = translator.toString(prog)
        if token in inQueue: return 
        q2format[token] = prog
        q.put((cost, token))
        inQueue.add(token)
    
    qadd(1.0, [boolSymbol])
    #print(boolSymbol)

    tn = len(testcases)
    terms = []
    while not q.empty():
        cost, progToken = q.get()
        prog = q2format[progToken]
        #print(cost, ":", progToken)
        #x=str(input())
        TryExtend = Extend(prog, Productions, cost)
        if len(TryExtend) == 0:
            rs = togroup(prog, testcases)
            score = sum(rs)
            if score > 0 and score < tn:
                terms.append(prog)
            continue
        
        for ext in TryExtend:
            if ext[0] < thres: qadd(ext[0], ext[1])
    
    return terms

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
            #if (debug): print(cm)
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

def unification(terms, boolSymbol):
    #terms = select(terms, testcases)
    meets = [runtest(term, testcases) for term in terms]

    def complete(conditions):
        tn = len(testcases)
        equi = [-1 for i in range(tn)]
        results = [togroup(prog, testcases) for prog in conditions]

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
    thres = 1.4
    decisions = []
    while True:
        decisions = searchDecision(thres, boolSymbol)
        if complete(decisions): break
        #print(thres)
        thres *= 1.2
    '''
    for term in terms:
        print(term)
        print(runtest(term))
    
    for term in decisions:
        print(term)
    '''
    
    #print(len(terms), len(decisions), len(testcases))

    prog = decisionTree(terms, decisions, testcases)
    progToken = translator.toString(prog)
    ans = FuncDefineStr[:-1] + " " + progToken + FuncDefineStr[-1]
    model = checker.check(ans)

    if model is not None:
        tc = resolve(model)
        #print(tc, evaluator.evaluate(prog, dict(zip(argList, tc))))
        #print(progToken)
        testcases.append(tc)
        return None
    return ans

def resolve(model):
    tc = []
    for arg in argList:
        x = checker.VarTable[arg2call[arg]]
        tc.append(model.eval(x, True).as_long())
    return tc

def solver(bmExpr, intSymbol, boolSymbol, _callExpr):
    global callExpr
    callExpr = _callExpr

    global checker
    checker=translator.ReadQuery(bmExpr)
    
    synExpr = None
    for expr in bmExpr:
        if expr[0] == "synth-fun":
            synExpr = expr
    for arg in synExpr[2]:
        argList.append(arg[0])
    
    global arg2call
    arg2call = dict(zip(argList, callExpr[1:]))
    global call2arg
    call2arg = dict(zip(callExpr[1:], argList))

    global FuncDefineStr
    FuncDefineStr = translator.toString(['define-fun'] + synExpr[1:4], ForceBracket = True)

    for noterm in synExpr[4]: #SynFunExpr[4] is the production rules
        Productions[noterm[0]] = noterm[2]
    generateValidInputs(100)
    #for tc in testcases:
    #    print(tc)

    while True:
        thres = 1.1
        while True:
            terms, oneshot = search(thres, intSymbol)
            if oneshot:
                #print(thres, terms)
                ans = unification(terms, boolSymbol)
                if ans is None: break
                return ans
            thres *= 1.2