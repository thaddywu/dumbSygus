import sys
import sexp
import pprint
import translator
import evaluator

testcases = []

bitvecShape = ['BitVec', ('Int', 64)]
argList = []
synExpr = []
FuncDefineStr = ""
Productions = {}
terms = []

def getBitvector(bv):
    type, item = bv
    assert type == bitvecShape
    return int(item)

def runtest(prog):
    result = []
    for tc in testcases:
        args, std = tc
        output = evaluator.evaluate(prog, zip(argList, args))
        result.append(int(output == std))
    return result

def formatize(token):
    return FuncDefineStr[:-1] + " " + token + FuncDefineStr[-1]

def extend(prog0, depth0, maxDepth):
    tryExtend = []
    return tryExtend

def iterSearch(maxDepth):
    termSet = set()
    BfsQueue = []
    scores = [0 for i in range()]
    while len(BfsQueue) > 0:
        prog, depth = BfsQueue.pop(0)
        token = translator.toString(prog)
        result = runtest(prog)
        if sum(result) > 0:
            terms.add(prog)
            scores = [x + y for x, y in zip(scores, result)]
            if sum(scores) == len(testcases): break
        
        tryExtend = extend(prog, depth, maxDepth)
        for cand in tryExtend:
            cprog, _ = cand
            token = translator.toString(cprog)
            if token not in termSet:
                termSet.add(token)
                
            
        

def solver(bmExpr):
    checker=translator.ReadQuery(bmExpr)
    for constraint in checker.Constraints:
        assert len(constraint[1]) == 3
        assert constraint[1][0] == "="
        assert constraint[1][1][0] == checker.synFunction.name
        input = []
        for arg in constraint[1][1][1:]:
            input += [getBitvector(arg)]

        output = getBitvector(constraint[1][2])
        testcases.append((input, output))
    
    
    for expr in bmExpr:
        if expr[0] == "synth-fun":
            synExpr = expr
    for arg in synExpr[2]:
        assert (arg[1] == bitvecShape)
        argList.append(arg[0])

    FuncDefineStr = translator.toString(['define-fun'] + synExpr[1:4], ForceBracket = True)

    for noterm in synExpr[4]: #SynFunExpr[4] is the production rules
        assert noterm[1] == bitvecShape
        Productions[noterm[0]] = noterm[2]
    
    