def evaluate(stmts, args):
    if type(stmts) != list:
        if type(stmts) == tuple: return int(stmts[1])
        return args[stmts] if stmts in args else stmts
    else:
        mnemonic = stmts[0]
        if mnemonic == "ite": return evaluate(stmts[2], args) if evaluate(stmts[1], args) else evaluate(stmts[3], args)
        elif mnemonic == "<": return (evaluate(stmts[1], args) < evaluate(stmts[2], args))
        elif mnemonic == "<=": return (evaluate(stmts[1], args) <= evaluate(stmts[2], args))
        elif mnemonic == ">": return (evaluate(stmts[1], args) > evaluate(stmts[2], args))
        elif mnemonic == ">=": return (evaluate(stmts[1], args) >= evaluate(stmts[2], args))
        elif mnemonic == "and": return (evaluate(stmts[1], args) and evaluate(stmts[2], args))
        elif mnemonic == "or": return (evaluate(stmts[1], args) or evaluate(stmts[2], args))
        elif mnemonic == "not": return (not evaluate(stmts[1], args))
        elif mnemonic == "+": return (evaluate(stmts[1], args) + evaluate(stmts[2], args))
        elif mnemonic == "-": return (evaluate(stmts[1], args) - evaluate(stmts[2], args))
        elif mnemonic == "*": return (evaluate(stmts[1], args) * evaluate(stmts[2], args))
        elif mnemonic == "mod": return (evaluate(stmts[1], args) % evaluate(stmts[2], args))
        elif mnemonic == "shr1": return (evaluate(stmts[1], args) >> 1)
        elif mnemonic == "shr4": return (evaluate(stmts[1], args) >> 4)
        elif mnemonic == "shr16": return (evaluate(stmts[1], args) >> 16)
        elif mnemonic == "shl1": return (evaluate(stmts[1], args) << 1) % 18446744073709551616
        elif mnemonic == "bvadd": return (evaluate(stmts[1], args) + evaluate(stmts[2], args)) % 18446744073709551616
        elif mnemonic == "bvand": return (evaluate(stmts[1], args) & evaluate(stmts[2], args))
        elif mnemonic == "bvor": return (evaluate(stmts[1], args) | evaluate(stmts[2], args))
        elif mnemonic == "bvxor": return (evaluate(stmts[1], args) ^ evaluate(stmts[2], args))
        elif mnemonic == "bvnot": return (evaluate(stmts[1], args) ^ 18446744073709551615)
        elif mnemonic == "if0": return evaluate(stmts[2], args) if evaluate(stmts[1], args) == 1 else evaluate(stmts[3], args)
        elif len(stmts) == 1: return evaluate(stmts[0], args)
        else: assert(False)

def cost(mnemonic):
    prob_table = {
        "ite": 100.5,
        "<" : 1.4,
        "<=" : 1.4,
        ">" : 1.6,
        ">=" : 1.6,
        "and" : 1.4,
        "or" : 1.4,
        "not" : 1.4,
        "+" : 1.4,
        "-" : 1.4,
        "*" : 1.5,
        "mod" : 1.5,
        "shr1" : 1.4,
        "shl1" : 1.4,
        "shr4" : 1.5,
        "shr16" : 1.7,
        "bvand" : 1.5,
        "bvor" : 1.5,
        "bvxor" : 1.5,
        "bvnot" : 1.5,
        "if0" : 100.5
    }
    return prob_table[mnemonic] if mnemonic in prob_table else 1.3