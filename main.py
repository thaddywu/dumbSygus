import sys
import sexp
import pprint
import translator
import bv
import brute
import clia

def stripComments(bmFile):
    noComments = '(\n'
    for line in bmFile:
        line = line.split(';', 1)[0]
        noComments += line
    return noComments + '\n)'

def mode(bmExpr):
    for expr in bmExpr:
        if type(expr) == list and len(expr) > 1 and expr[0] == "set-logic":
            return expr[1]

def BVSpecific(bmExpr):
    synExpr = None
    for expr in bmExpr:
        if expr[0] == "synth-fun": synExpr = expr
    if len(synExpr[4]) > 1: return False
    body = synExpr[4][0]
    mnemonic = body[0]
    if body[1][0] != 'BitVec': return False
    for rule in body[2]:
        if rule[0] == "if0": return True
    return False

def findCallExpr(cons, func):
    if type(cons) != list: return None
    if cons[0] == func: return cons
    for item in cons[1:]:
        ret = findCallExpr(item, func)
        if ret is not None: return ret

def matchCallExpr(cons, func, expr):
    if type(cons) != list: return True
    if cons[0] == func:
        return cons == expr
    for item in cons[1:]:
        if not matchCallExpr(item, func, expr): return False
    return True

def CLIASpecific(bmExpr):
    synExpr = None
    for expr in bmExpr:
        if len(expr) == 0: continue
        if expr[0] == "synth-fun": synExpr = expr
    if len(synExpr[4]) != 2: return None

    # only one int and one bool non-terminant allowed
    boolBody, intBody = [], []
    if synExpr[4][0][1] == "Int" and synExpr[4][1][1] == "Bool":
        boolBody, intBody = synExpr[4][1], synExpr[4][0]
    elif synExpr[4][1][1] == "Int" and synExpr[4][0][1] == "Bool":
        boolBody, intBody = synExpr[4][0], synExpr[4][1]
    else: return None

    func = synExpr[1]

    if synExpr[3] != "Int": return None
    
    # assert func is only called with the same input
    funcExpr = None
    for expr in bmExpr:
        if len(expr) == 0: continue
        if expr[0] == "constraint":
            if funcExpr is None:
                funcExpr = findCallExpr(expr[1], func)
            if funcExpr is not None:
                if not matchCallExpr(expr[1], func, funcExpr): return None
    if funcExpr is not None:
        for item in funcExpr[1:]:
            if type(item) == list: return None
        
    #check ite exists
    for rule in intBody[2]:
        if rule[0] == "ite": return (intBody[0], boolBody[0], funcExpr)
    return None


if __name__ == '__main__':
    benchmarkFile = open(sys.argv[1])
    bm = stripComments(benchmarkFile)
    bmExpr = sexp.sexp.parseString(bm, parseAll=True).asList()[0] #Parse string to python list
    if mode(bmExpr) in ['BV']:
        if BVSpecific(bmExpr):
            print(bv.solver(bmExpr))
        else:
            print(brute.solver(bmExpr))
    else:
        ret = CLIASpecific(bmExpr)
        if ret is not None:
            intSymbol, boolSymbol, callExpr = ret
            print(clia.solver(bmExpr, intSymbol, boolSymbol, callExpr))
        else:
            print(brute.solver(bmExpr))
