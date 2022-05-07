#!/usr/bin/env python3
from abc import ABC, abstractmethod
from dataclasses import dataclass, field
from typing import *
from z3 import *
import random
from enum import Enum, auto
from imp_machine import *

@dataclass
class Machine(ABC):
    """The class of machines supported by concolic execution"""
    ops: Any
    # states: Any # class of states; NOTE: this is implicitly defined by the "type" of init_state, halt_state, and delta
    halt_state: Any

    @abstractmethod
    def init_state(self, inputs):
        """Returns initial state for the machine based on an optional input setting."""
        pass

    # state * op -> state * [ctlflow]
    @abstractmethod
    def delta(self, state, op):
        """The machine's transition function"""
        pass

    @abstractmethod
    def path_cond(self, path):
        """Computes the path condition of an execution path on the machine. The
           path is given by a list of (state * effect)."""
        pass

    @abstractmethod
    def free_vars(self, prog):
        """Computes the free vars of a program"""
        pass

    @abstractmethod
    def random_assignment(self, typed_free_vars):
        """Generates a random assignment of values to free variables given their
        types"""
        pass 
   
class Effect(Enum):
    # control flow effects
    BrLeft = auto()
    BrRight = auto()
    Jmp = auto()
    Next = auto()
    # Call = auto()
    # Ret = auto()
    Halt = auto()
    Reset = auto() 

    # i/o effects
    Print = auto()

@dataclass
class Program:
    """A fancy sequence of operations with associated navigation operations"""
    machine: Any# machine for which this is a program
    ops: List[Any] # sequence of operations
    start_location = 0 # location of program in memory, defaults to 0 for PIE
    op_ptr = 0 # points to the current operation

    def __post_init__(self):
        assert(self.ops) # cannot start halted

   
    def cur_inst(self):
        try:
            return self.ops[self.op_ptr]
        except:
            return None

    def navigate(self, ctlflow):
        """Updates op_ptr as specified by a ctlflow effect"""
        match ctlflow:
            case [(Effect.BrLeft | Effect.BrRight), _, tgt] | [Effect.Jmp, tgt]:
                self.op_ptr = tgt
            case Effect.Next | [Effect.Print, _]:
                if self.op_ptr + 1 < len(self.ops):
                    self.op_ptr += 1
                else:
                    self.op_ptr = None # halt if we fall off the end of the program
            case Effect.Halt:
                self.op_ptr = None
            case Effect.Reset: # TODO: is this how I want this to work?
                self.op_ptr = 0
            case _:
                raise(Exception("Invalid control flow"))

    def free_vars(self):
        """Computes the free (input) variables of the program"""
        return self.machine.free_vars(self.ops)

@dataclass
class ExecEngine:
    """"""
    machine: Machine
    program: Program
    cur_state: Any = field(repr=True, init=False)
    observed: Any = field(default_factory=list) # pairs of seen execution paths and their path conditions
    cur_path: Any = field(default_factory=list) # The execution path is a list of (state * ctlflow)
                                                # a ctlflow is something like ip+1, jmp(target),
                                                # br_left(cond), br_right(cond)

    # FIXME: needed?
    # def __post_init__(self):
    #     self.cur_state = self.machine.init_state

    def execute(self, assignment):
        """Takes an assignment of free variables to values, executes the program with
           these values plugged in, and returns the observed execution path"""
        self.program.navigate(Effect.Reset) # make sure program is seeked to 0
        self.cur_state = self.machine.init_state(assignment)
        self.cur_path = [] # zero out the path

        while self.cur_state != self.machine.halt_state:
            action = self.program.cur_inst()
            if action:
                (next_state, ctlflow) = self.machine.delta(self.cur_state, action)
                self.cur_path += [(next_state, ctlflow)] # keep track of where we've gone
                self.cur_state = next_state # update execution state
                self.program.navigate(ctlflow) # update the position in the program
            else:
                self.cur_state = None # TODO: replace with actual haltstate
                break
        return self.cur_path

    def analyze(self, target_prop: Callable[..., Bool]):
        # Analysis proceeds by randomly generating a seed input from the broadest
        # possible domain of program inputs; this may not nessarily be the strict
        # domain specified by the paper specification of the program, but rather
        # the maximal domain allowed by machine's built-in protection scheme.
        input = self.machine.random_assignment(self.program.free_vars())
        # Analysis continues by continually generating a new input for
        # the program by the following scheme. For each run of the
        # program, we will record its execution path. The execution path
        # is a list of (state * ctlflow)

        # a ctlflow is something like ip+1, jmp(target), br_left(cond),
        # br_right(cond)

        # The path condition is computed by the conjunction
        # /\_(p in Path) [ if p = br_left(cond) {cond} elif p = br_right(cond) { !cond } else true ]

        # It would also be nice to have functionality allowing us to instrument
        # the path conditions with assertions at any position.
        while input is not unsat:
            print(f"iter with {input}")
            p = self.execute(input)

            if target_prop(p):
                print(f"SUCCESS with input = {input}")
                break
            g = self.machine.path_cond(p)
            self.observed += [g]
            s = z3.Solver()
            s.add(And([Not(c) for c in self.observed]))
            if s.check():
                m = s.model()
                for v in m.decls():
                    input[str(v)] = m[v]
            else:
                print("FAILED: all paths exhausted")
                break
