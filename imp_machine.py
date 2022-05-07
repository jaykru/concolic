import random
from concolic import *
from dataclasses import dataclass
from enum import Enum, auto
from typing import *
from z3 import *
#import frozendict # TODO: use this for states

@dataclass
class ImpLoc:
    name: str

    def __hash__(self):
        return hash(self.name)

# @dataclass
# class ImpImm:
#     val: int

@dataclass
class ImpState:
    conc: Dict[str, Any]
    sym: Dict[str, Any]

    def get_both(self, var):
        return (self.conc.get(var), self.sym.get(var))

    @staticmethod
    def new_state(input_assignment):
        conc = {}
        sym = {}
        for (var, val) in input_assignment.items():
            if type(val) is type(0):
                conc[var] = val
            else:
                conc[var] = val.as_long() # FIXME: this is supplied by z3 so we probably need to cast it from an AST?
            sym[var] = z3.Int(var)
        return ImpState(conc, sym)

class ImpOp(Enum):
    Add = auto()
    Sub = auto()
    Mul = auto()
    Div = auto()
    Goto = auto()
    Jnz = auto()
    Set = auto()
    Put = auto()
    Puts = auto()
    Halt = auto()

@dataclass
class Symgen:
    ctr: int = 0

    def gensym(self):
        sym = f"u{self.ctr}"
        self.ctr += 1
        return sym

# @dataclass
# class ImpMachine(Machine):

imp_ops = [ op for op in ImpOp.__members__ ]

class ImpMachine(Machine):
    g: Symgen = Symgen()

    def delta(self, state, op):
        """Given a state (which is a pair of a (hash table ImpLoc -> ImpVal) and a hash table (ImpLoc -> z3.formula)) and an operation,
        produce and return the updated state
        
        Type: state * op -> maybe (state * [ctlflow])"""
        match op:
            case [ImpOp.Add, ImpLoc(loc1), ImpLoc(loc2)]:
                v1, v1s = state.get_both(loc1)
                v2, v2s = state.get_both(loc2)
                match (v1, v2, v1s, v2s):
                    case (None, _, _, _) | (_, None, _, _) | (_, _, None, _) | (_, _, _, None):
                        raise(Exception("invalid Add instruction"))
                    case _:
                        state.conc[loc1] = v1 + v2
                        state.sym[loc1] = z3.simplify(v1s + v2s)
                return (state, Effect.Next)

            case [ImpOp.Add, ImpLoc(loc), v]:
                v1, v1s = state.get_both(loc)
                match v1, v1s:
                    case (None, _) | (_, None):
                        raise(Exception("invalid Add instruction"))
                    case _:
                        state.conc[loc] = v1 + v
                        state.sym[loc] = v1s + v
                return (state, Effect.Next)


            case [ImpOp.Sub, ImpLoc(loc1), ImpLoc(loc2)]:
                v1, v1s = state.get_both(loc1)
                v2, v2s = state.get_both(loc2)
                match (v1, v1s, v2, v2s):
                    case (None, _, _, _) | (_, None, _, _) | (_, _, None, _) | (_, _, _, None):
                        raise(Exception("invalid Sub instruction"))
                    case _:
                        state.conc[loc1] = v1 - v2
                        state.sym[loc1] = v1s - v2s
                return (state, Effect.Next)

            case [ImpOp.Sub, ImpLoc(loc), v]:
                v1, v1s = state.get_both(loc) # FIXME: make sure this is a safe get
                match (v1, v1s):
                    case (None, _) | (_, None):
                        raise(Exception("invalid Sub instruction"))
                    case _:
                        state.conc[loc] = v1 - v
                        state.sym[loc] = v1s - v
                return (state, Effect.Next)

            case [ImpOp.Mul, ImpLoc(loc1), ImpLoc(loc2)]:
                v1, v1s = state.get_both(loc1)
                v2, v2s = state.get_both(loc2)
                match (v1, v1s, v2, v2s):
                    case (None, _, _, _) | (_, None, _, _) | (_, _, None, _) | (_, _, _, None):
                        raise(Exception("invalid Mul instruction"))
                    case _:
                        state.conc[loc1] = v1 * v2
                        state.sym[loc1] = state.conc[loc1]
                return (state, Effect.Next)

            case [ImpOp.Mul, ImpLoc(loc), v]:
                v1, v1s = state.get_both(loc) # FIXME: make sure this is a safe get
                match (v1, v1s):
                    case (None, _) | (_, None):
                        raise(Exception("invalid Mul instruction"))
                    case _:
                        state.conc[loc] = v1 * v
                        state.sym[loc] = state.conc[loc]
                return (state, Effect.Next)

            case [ImpOp.Div, ImpLoc(loc1), ImpLoc(loc2)]:
                v1, v1s = state.get_both(loc1)
                v2, v2s = state.get_both(loc2)
                match (v1, v1s, v2, v2s):
                    case (None, _, _, _) | (_, None, _, _) | (_, _, None, _) | (_, _, _, None):
                        raise(Exception("invalid Div instruction"))
                    case _:
                        try:
                            state.conc[loc1] = v1 / v2
                        except:
                            raise(Exception("Division by zero encountered.")) # FIXME: do something nicer here.
                        state.sym[loc1] = state.conc[loc1]
                return (state, Effect.Next)

            case [ImpOp.Div, ImpLoc(loc), v]:
                v1, v1s = state.get_both(loc) # FIXME: make sure this is a safe get
                match (v1, v1s):
                    case (None, _) | (_, None):
                        raise(Exception("invalid Div instruction"))
                    case _:
                        try:
                            state.conc[loc] = v1 / v
                        except:
                            raise(Exception("Division by zero encountered."))
                        state.sym[loc] = state.conc[loc]
                return (state, Effect.Next)

            case [ImpOp.Goto, tgt]:
                return (state, [Effect.Jmp, tgt]) # no state.conc change is required, only results in a Effect

            case [ImpOp.Jnz, discriminee, left_tgt, right_tgt]:
                match discriminee:
                    case ImpLoc(l):
                        # TODO: revisit this, does it still make sense?
                        val = state.conc.get(l)
                    
                        if(val != 0):
                            ctlflow = [Effect.BrLeft, discriminee, left_tgt]
                            # FIXME: should we change the state.conc here? I think just returning
                            # the ctlflow should be ok
                        else:
                            ctlflow = [Effect.BrRight, discriminee, right_tgt]
                        return (state, ctlflow)
                    case _:
                        raise(Exception("invalid Jnz instruction"))

            case [ImpOp.Set, ImpLoc(loc1), ImpLoc(loc2)]:
                v, vs = state.get_both(loc2)
                match (v, vs):
                    case (None, _) | (_, None):
                        raise(Exception("invalid Set instruction"))
                    case _:
                        state.conc[loc1] = v
                        state.sym[loc1] = vs
                        return (state, Effect.Next)

            case [ImpOp.Set, ImpLoc(loc), v]:
                state.conc[loc] = v
                state.sym[loc] = z3.Int(self.g.gensym()) # TODO: revisit this
                return (state, Effect.Next)

            case [ImpOp.Put, ImpLoc(loc)]:
                v = state.conc[loc] # FIXME: make sure this is a safe get
                match v:
                    case None:
                        raise(Exception("invalid instruction")) 
                    case _:
                        print(v)
                return (state, Effect.Next)

            case [ImpOp.Put, v]:
                print(v)
                return (state, Effect.Next)

            case [ImpOp.Puts, s]:
                print(s)
                return (state, [Effect.Print, s])

            case ImpOp.Halt | [ImpOp.Halt]:
                print("Machine halted.")
                return (None, Effect.Halt)

            case _:
                raise(Exception(f"Invalid instruction {op}")) 


    def random_assignment(self, free_vars):
        assignment = {}
        for var in free_vars:
            assignment[var] = random.randrange(0,2**8 + 1)
        return assignment
    
    def free_vars(self, program):
        bound_vars = set()
        free_vars = set()
        for op in program:
            match op:
                case [ImpOp.Set, ImpLoc(l), v]:
                    if l not in free_vars:
                        bound_vars.add(l)
                    match v:
                        case ImpLoc(l2):
                            if l2 not in bound_vars:
                                free_vars.add(l2)
                        case _:
                            pass
                case [_, ImpLoc(l1), ImpLoc(l2)]:
                    if l1 not in bound_vars:
                        free_vars.add(l1)
                    if l2 not in bound_vars:
                        free_vars.add(l2)
                case [_, ImpLoc(l), *_]:
                    if l not in bound_vars:
                        free_vars.add(l)
                case _:
                    pass
                    # raise(Exception("Incomplete pattern match"))
        return free_vars

    def path_cond(self,path):
        formulae = []
        for entry in path:
            match entry:
                case (state, ctlflow):
                            match ctlflow:
                                case [Effect.BrLeft, d, _]:
                                    match d:
                                        case ImpLoc(var):
                                            symval = state.sym[var]
                                            formulae.append(symval != 0)
                                case [Effect.BrRight, d, _]:
                                    match d:
                                        case ImpLoc(var):
                                            symval = state.sym[var]
                                            formulae.append(symval == 0)
                                case _:
                                    pass # not necessary to write, but it makes me feel better
        return And(formulae)

    def init_state(self, input): 
        return ImpState.new_state(input)

imp_machine = ImpMachine(ops = ImpOp,
                         halt_state = None)

def vars_of(prog):
    vars = set()
    for op in prog:
        match op:
            case [ImpOp.Set, ImpLoc(l), _]:
                vars.add(l)
            case [_, ImpLoc(l1), ImpLoc(l2)]:
                vars.add(l1)
                vars.add(l2)
            case [_, ImpLoc(l), *_]:
                vars.add(l)
    return vars


def memo_wrap(f):
    memo = {}
    def wrapped_f(input, memo_info):
        saved = memo.get(memo_info)
        if saved:
            return saved
        else:
            val = f(input)
            memo[memo_info] = val
            return val
    return wrapped_f

vars_of = memo_wrap(vars_of)

g: Symgen = Symgen()
def gen_imp_prog(target_len, vars):
    prog = []
    for cur_len in range(0,target_len):
        choice = random.randrange(0, 100)
        if choice in range(0,10):
            # branch
            discs = []
            discs.extend(vars)
            discs.append(g.gensym())
            disc = random.randrange(0,len(vars)+1)
            disc = discs[disc]
            gen_inst = [ImpOp.Jnz, ImpLoc(disc), random.randrange(0,target_len), random.randrange(0,target_len)] 
        else:
            all_vars_so_far = list(set(vars).union(vars_of(prog[0:-1], cur_len), vars_of([prog[-1:0]], cur_len)))
            target = ImpLoc(all_vars_so_far[random.randrange(0,len(all_vars_so_far))])
            if choice in range(0, 30) or choice in range(60,99):
                # add

                gen_inst = [ImpOp.Add, target, random.randint(0,69420)]

            elif choice in range(30,40):
                # sub
                gen_inst = [ImpOp.Sub, target, random.randint(0,69420)]

            elif choice in range(40,50):
                # set
                gen_inst = [ImpOp.Set, target, random.randint(0,69420)]

            elif choice in range(50,60):
                # put
                gen_inst = [ImpOp.Put, target]

            elif choice in range(99,100):
                gen_inst = [ImpOp.Puts, "flag"]

        prog.append(gen_inst)
    return prog
