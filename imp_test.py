from imp_machine import ImpOp, ImpLoc, imp_machine, gen_imp_prog
from concolic import *

def we_won(path):
    return any([effect == [Effect.Print, "flag"] for (_, effect) in path])

l6 = "l6"
ret = "ret"
l10 = "l10"
l7 = "l7"
l4 = "l4"
l5 = "l5"
l1 = "l1"
l2 = "l2"
l3 = "l3"

runtime_error_test = [[ImpOp.Jnz, ImpLoc(l6), 3, 1],
                      [ImpOp.Set, ImpLoc(ret), 0],
                      [ImpOp.Halt],
                      [ImpOp.Jnz, ImpLoc(l7), 7, 4],
                      # ret = l4 * l5
                      [ImpOp.Set, ImpLoc(ret), ImpLoc(l4)],
                      [ImpOp.Mul, ImpLoc(ret), ImpLoc(l5)],
                      [ImpOp.Halt],
                      # if (l1/l2)...
                      [ImpOp.Set, ImpLoc(l10), ImpLoc(l1)],
                      [ImpOp.Div, ImpLoc(l10), ImpLoc(l2)],
                      [ImpOp.Sub, ImpLoc(l10), ImpLoc(l3)],
                      [ImpOp.Jnz, ImpLoc(l10), 11, 14],
                      # l3 != l1/l2 : ret = l4 + l5
                      [ImpOp.Set, ImpLoc(ret), ImpLoc(l4)],
                      [ImpOp.Div, ImpLoc(ret), ImpLoc(l5)],
                      [ImpOp.Halt],
                      # l3 == l1/l2; ret = l4 + l5
                      [ImpOp.Set, ImpLoc(ret), ImpLoc(l4)],
                      [ImpOp.Add, ImpLoc(ret), ImpLoc(l5)],
                      [ImpOp.Halt]]

def main():
    l1 = "l1"
    l2 = "l2"
    l3 = "l3"
    test_prog = [[ImpOp.Add, ImpLoc(l1), 1],
                 [ImpOp.Jnz, ImpLoc(l1), 6, 2],
                 [ImpOp.Jnz, ImpLoc(l2), 6, 5],
                 [ImpOp.Puts, "flag"],
                 ImpOp.Halt,
                 [ImpOp.Jnz, ImpLoc(l3), 6, 3],
                 [ImpOp.Puts, "better luck next time kid"]]

    # test_prog_2 = gen_imp_prog(10000, ["l1","l2","l3","l4","l5"])
    
    e = ExecEngine(machine=imp_machine,
                   program=Program(imp_machine, test_prog))
    e.analyze(target_prop=we_won)

if __name__ == "__main__":
    main()
