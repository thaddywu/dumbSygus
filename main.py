import sys
import sexp
import pprint
import translator
import bv

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

if __name__ == '__main__':
    benchmarkFile = open(sys.argv[1])
    bm = stripComments(benchmarkFile)
    bmExpr = sexp.sexp.parseString(bm, parseAll=True).asList()[0] #Parse string to python list
    if mode(bmExpr) in ['BV']:
        print(bv.solver(bmExpr))