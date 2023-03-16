import sys
import time

import argparse

class Variable:
    '''Class for defining CSP variables.

      On initialization the variable object can be given a name and a
      list containing variable's domain of values. You can reset the
      variable's domain if you want to solve a similar problem where
      the domains have changed.

      To support CSP propagation, the class also maintains a current
      domain for the variable. Values pruned from the variable domain
      are removed from the current domain but not from the original
      domain. Values can be also restored.
    '''

    undoDict = dict()             #stores pruned values indexed by a
                                        #(variable,value) reason pair
    def __init__(self, name, domain):
        '''Create a variable object, specifying its name (a
        string) and domain of values.
        '''
        self._name = name                #text name for variable
        self._dom = list(domain)         #Make a copy of passed domain
        self._curdom = list(domain)      #using list
        self._value = None

    def __str__(self):
        return "Variable {}".format(self._name)

    def domain(self):
        '''return copy of variable domain'''
        return(list(self._dom))

    def domainSize(self):
        '''Return the size of the domain'''
        return(len(self.domain()))

    def resetDomain(self, newdomain):
        '''reset the domain of this variable'''
        self._dom = newdomain

    def getValue(self):
        return self._value

    def setValue(self, value):
        if value != None and not value in self._dom:
            print("Error: tried to assign value {} to variable {} that is not in {}'s domain".format(value,self._name,self._name))
        else:
            self._value = value    

    def unAssign(self):
        self.setValue(None)

    def isAssigned(self):
        return self.getValue() != None

    def name(self):
        return self._name

    def curDomain(self):
        '''return copy of variable current domain. But if variable is assigned
           return just its assigned value (this makes implementing hasSupport easier'''
        if self.isAssigned():
            return([self.getValue()])
        return(list(self._curdom))

    def curDomainSize(self):
        '''Return the size of the current domain'''
        if self.isAssigned():
            return(1)
        return(len(self._curdom))

    def inCurDomain(self, value):
        '''check if value is in current domain'''
        if self.isAssigned():
            return(value==self.getValue())
        return(value in self._curdom)

    def pruneValue(self, value, reasonVar, reasonVal):
        '''Remove value from current domain'''
        try:
            self._curdom.remove(value)
        except:
            print("Error: tried to prune value {} from variable {}'s domain, but value not present!".format(value, self._name))
        dkey = (reasonVar, reasonVal)
        if not dkey in Variable.undoDict:
            Variable.undoDict[dkey] = []
        Variable.undoDict[dkey].append((self, value))

    def restoreVal(self, value):
        self._curdom.append(value)

    def restoreCurDomain(self):
        self._curdom = self.domain()

    def reset(self):
        self.restoreCurDomain()
        self.unAssign()

    def dumpVar(self):
        print("Variable\"{}={}\": Dom = {}, CurDom = {}".format(self._name, self._value, self._dom, self._curdom))

    @staticmethod
    def clearUndoDict():
        undoDict = dict()

    @staticmethod
    def restoreValues(reasonVar, reasonVal):
        dkey = (reasonVar, reasonVal)
        if dkey in Variable.undoDict:
            for (var,val) in Variable.undoDict[dkey]:
                var.restoreVal(val)
            del Variable.undoDict[dkey]



#implement various types of constraints
class Constraint:
    '''Base class for defining constraints. Each constraint can check if
       it has been satisfied, so each type of constraint must be a
       different class. For example a constraint of notEquals(V1,V2)
       must be a different class from a constraint of
       greaterThan(V1,V2), as they must implement different checks of
       satisfaction.

       However one can define a class of general table constraints, as
       below, that can capture many different constraints.

       On initialization the constraint's name can be given as well as
       the constraint's scope. IMPORTANT, the scope is ordered! E.g.,
       the constraint greaterThan(V1,V2) is not the same as the
       contraint greaterThan(V2,V1).
    '''
    def __init__(self, name, scope):
        '''create a constraint object, specify the constraint name (a
        string) and its scope (an ORDERED list of variable
        objects).'''
        self._scope = list(scope)
        self._name = "baseClass_" + name  #override in subconstraint types!

    def scope(self):
        return list(self._scope)

    def arity(self):
        return len(self._scope)

    def numUnassigned(self):
        i = 0
        for var in self._scope:
            if not var.isAssigned():
                i += 1
        return i

    def unAssignedVars(self):
        return [var for var in self.scope() if not var.isAssigned()]

    # def check(self):
    #     util.raiseNotDefined()

    def name(self):
        return self._name

    def __str__(self):
        return "Cnstr_{}({})".format(self.name(), map(lambda var: var.name(), self.scope()))

    def printConstraint(self):
        print("Cons: {} Vars = {}".format(
            self.name(), [v.name() for v in self.scope()]))


#object for holding a constraint problem
class CSP:
    '''CSP class groups together a set of variables and a set of
       constraints to form a CSP problem. Provides a usesful place
       to put some other functions that depend on which variables
       and constraints are active'''

    def __init__(self, name, variables, constraints):
        '''create a CSP problem object passing it a name, a list of
           variable objects, and a list of constraint objects'''
        self._name = name
        self._variables = variables
        self._constraints = constraints

        #some sanity checks
        varsInCnst = set()
        for c in constraints:
            varsInCnst = varsInCnst.union(c.scope())
        for v in variables:
            if v not in varsInCnst:
                print("Warning: variable {} is not in any constraint of the CSP {}".format(v.name(), self.name()))
        for v in varsInCnst:
            if v not in variables:
                print("Error: variable {} appears in constraint but specified as one of the variables of the CSP {}".format(v.name(), self.name()))

        self.constraints_of = [[] for i in range(len(variables))]
        for c in constraints:
            for v in c.scope():
                i = variables.index(v)
                self.constraints_of[i].append(c)

    def name(self):
        return self._name

    def variables(self):
        return list(self._variables)

    def constraints(self):
        return list(self._constraints)

    def constraintsOf(self, var):
        '''return constraints with var in their scope'''
        try:
            i = self.variables().index(var)
            return list(self.constraints_of[i])
        except:
            print("Error: tried to find constraint of variable {} that isn't in this CSP {}".format(var, self.name()))

    def unAssignAllVars(self):
        '''unassign all variables'''
        for v in self.variables():
            v.unAssign()

    def check(self, solutions):
        '''each solution is a list of (var, value) pairs. Check to see
           if these satisfy all the constraints. Return list of
           erroneous solutions'''

        #save values to restore later
        current_values = [(var, var.getValue()) for var in self.variables()]
        errs = []

        for s in solutions:
            s_vars = [var for (var, val) in s]

            if len(s_vars) != len(self.variables()):
                errs.append([s, "Solution has incorrect number of variables in it"])
                continue

            if len(set(s_vars)) != len(self.variables()):
                errs.append([s, "Solution has duplicate variable assignments"])
                continue

            if set(s_vars) != set(self.variables()):
                errs.append([s, "Solution has incorrect variable in it"])
                continue

            for (var, val) in s:
                var.setValue(val)

            for c in self.constraints():
                if not c.check():
                    errs.append([s, "Solution does not satisfy constraint {}".format(c.name())])
                    break

        for (var, val) in current_values:
            var.setValue(val)

        return errs
    
    def __str__(self):
        return "CSP {}".format(self.name())



class TableConstraint(Constraint):
    '''General type of constraint that can be use to implement any type of
       constraint. But might require a lot of space to do so.

       A table constraint explicitly stores the set of satisfying
       tuples of assignments.'''

    def __init__(self, name, scope, satisfyingAssignments):
        '''Init by specifying a name and a set variables the constraint is over.
           Along with a list of satisfying assignments.
           Each satisfying assignment is itself a list, of length equal to
           the number of variables in the constraints scope.
           If sa is a single satisfying assignment, e.g, sa=satisfyingAssignments[0]
           then sa[i] is the value that will be assigned to the variable scope[i].


           Example, say you want to specify a constraint alldiff(A,B,C,D) for
           three variables A, B, C each with domain [1,2,3,4]
           Then you would create this constraint using the call
           c = TableConstraint('example', [A,B,C,D],
                               [[1, 2, 3, 4], [1, 2, 4, 3], [1, 3, 2, 4],
                                [1, 3, 4, 2], [1, 4, 2, 3], [1, 4, 3, 2],
                                [2, 1, 3, 4], [2, 1, 4, 3], [2, 3, 1, 4],
                                [2, 3, 4, 1], [2, 4, 1, 3], [2, 4, 3, 1],
                                [3, 1, 2, 4], [3, 1, 4, 2], [3, 2, 1, 4],
                                [3, 2, 4, 1], [3, 4, 1, 2], [3, 4, 2, 1],
                                [4, 1, 2, 3], [4, 1, 3, 2], [4, 2, 1, 3],
                                [4, 2, 3, 1], [4, 3, 1, 2], [4, 3, 2, 1]])
          as these are the only assignments to A,B,C respectively that
          satisfy alldiff(A,B,C,D)
        '''

        Constraint.__init__(self,name, scope)
        self._name = "TableCnstr_" + name
        self.satAssignments = satisfyingAssignments

    def check(self):
        '''check if current variable assignments are in the satisfying set'''
        assignments = []
        for v in self.scope():
            if v.isAssigned():
                assignments.append(v.getValue())
            else:
                return True
        return assignments in self.satAssignments

    def hasSupport(self, var,val):
        '''check if var=val has an extension to an assignment of all variables in
           constraint's scope that satisfies the constraint. Important only to
           examine values in the variable's current domain as possible extensions'''
        if var not in self.scope():
            return True   #var=val has support on any constraint it does not participate in
        vindex = self.scope().index(var)
        found = False
        for assignment in self.satAssignments:
            if assignment[vindex] != val:
                continue   #this assignment can't work it doesn't make var=val
            found = True   #Otherwise it has potential. Assume found until shown otherwise
            for i, v in enumerate(self.scope()):
                if i != vindex and not v.inCurDomain(assignment[i]):
                    found = False  #Bummer...this assignment didn't work it assigns
                    break          #a value to v that is not in v's curDomain
                                   #note we skip checking if val in in var's curDomain
            if found:     #if found still true the assigment worked. We can stop
                break
        return found     #either way found has the right truth value

def findvals(remainingVars, assignment, finalTestfn, partialTestfn=lambda x: True):
    '''Helper function for finding an assignment to the variables of a constraint
       that together with var=val satisfy the constraint. That is, this
       function looks for a supporing tuple.

       findvals uses recursion to build up a complete assignment, one value
       from every variable's current domain, along with var=val.

       It tries all ways of constructing such an assignment (using
       a recursive depth-first search).

       If partialTestfn is supplied, it will use this function to test
       all partial assignments---if the function returns False
       it will terminate trying to grow that assignment.

       It will test all full assignments to "allVars" using finalTestfn
       returning once it finds a full assignment that passes this test.

       returns True if it finds a suitable full assignment, False if none
       exist. (yes we are using an algorithm that is exactly like backtracking!)'''

    # print "==>findvars([",
    # for v in remainingVars: print v.name(), " ",
    # print "], [",
    # for x,y in assignment: print "({}={}) ".format(x.name(),y),
    # print ""

    #sort the variables call the internal version with the variables sorted
    remainingVars.sort(reverse=True, key=lambda v: v.curDomainSize())
    return findvals_(remainingVars, assignment, finalTestfn, partialTestfn)

def findvals_(remainingVars, assignment, finalTestfn, partialTestfn):
    '''findvals_ internal function with remainingVars sorted by the size of
       their current domain'''
    if len(remainingVars) == 0:
        return finalTestfn(assignment)
    var = remainingVars.pop()
    for val in var.curDomain():
        assignment.append((var, val))
        if partialTestfn(assignment):
            if findvals_(remainingVars, assignment, finalTestfn, partialTestfn):
                return True
        assignment.pop()   #(var,val) didn't work since we didn't do the return
    remainingVars.append(var)
    return False


class NValuesConstraint(Constraint):
    '''NValues constraint over a set of variables.  Among the variables in
       the constraint's scope the number that have been assigned
       values in the set 'required_values' is in the range
       [lower_bound, upper_bound] (lower_bound <= #of variables
       assigned 'required_value' <= upper_bound)

       For example, if we have 4 variables V1, V2, V3, V4, each with
       domain [1, 2, 3, 4], then the call
       NValuesConstraint('test_nvalues', [V1, V2, V3, V4], [1,4], 2,
       3) will only be satisfied by assignments such that at least 2
       the V1, V2, V3, V4 are assigned the value 1 or 4, and at most 3
       of them have been assigned the value 1 or 4.

    '''

    def __init__(self, name, scope, required_values, lower_bound, upper_bound):
        Constraint.__init__(self,name, scope)
        self._name = "NValues_" + name
        self._required = required_values
        self._lb = lower_bound
        self._ub = upper_bound

    def check(self):
        assignments = []
        for v in self.scope():
            if v.isAssigned():
                assignments.append(v.getValue())
            else:
                return True
        rv_count = 0

        #print "Checking {} with assignments = {}".format(self.name(), assignments)

        for v in assignments:
            if v in self._required:
                rv_count += 1

        #print "rv_count = {} test = {}".format(rv_count, self._lb <= rv_count and self._ub >= rv_count)


        return self._lb <= rv_count and self._ub >= rv_count

    def hasSupport(self, var, val):
        '''check if var=val has an extension to an assignment of the
           other variable in the constraint that satisfies the constraint

           HINT: check the implementation of AllDiffConstraint.hasSupport
                 a similar approach is applicable here (but of course
                 there are other ways as well)
        '''
        if var not in self.scope():
            return True   #var=val has support on any constraint it does not participate in

        #define the test functions for findvals
        def valsOK(l):
            '''tests a list of assignments which are pairs (var,val)
               to see if they can satisfy this sum constraint'''
            rv_count = 0
            vals = [val for (var, val) in l]
            for v in vals:
                if v in self._required:
                    rv_count += 1
            least = rv_count + self.arity() - len(vals)
            most =  rv_count
            return self._lb <= least and self._ub >= most
        varsToAssign = self.scope()
        varsToAssign.remove(var)
        x = findvals(varsToAssign, [(var, val)], valsOK, valsOK)
        return x

class IfAllThenOneConstraint(Constraint):
    '''if each variable in left_side equals each value in left_values 
    then one of the variables in right side has to equal one of the values in right_values. 
    hasSupport tested only, check() untested.'''
    def __init__(self, name, left_side, right_side, left_values, right_values):
        Constraint.__init__(self,name, left_side+right_side)
        self._name = "IfAllThenOne_" + name
        self._ls = left_side
        self._rs = right_side
        self._lv = left_values
        self._rv = right_values

class UnassignedVars:
    '''class for holding the unassigned variables of a CSP. We can extract
       from, re-initialize it, and return variables to it.  Object is
       initialized by passing a select_criteria (to determine the
       order variables are extracted) and the CSP object.

       select_criteria = ['random', 'fixed', 'mrv'] with
       'random' == select a random unassigned variable
       'fixed'  == follow the ordering of the CSP variables (i.e.,
                   csp.variables()[0] before csp.variables()[1]
       'mrv'    == select the variable with minimum values in its current domain
                   break ties by the ordering in the CSP variables.
    '''
    def __init__(self, select_criteria, csp):
        if select_criteria not in ['random', 'fixed', 'mrv']:
            pass #print "Error UnassignedVars given an illegal selection criteria {}. Must be one of 'random', 'stack', 'queue', or 'mrv'".format(select_criteria)
        self.unassigned = list(csp.variables())
        self.csp = csp
        self._select = select_criteria
        if select_criteria == 'fixed':
            #reverse unassigned list so that we can add and extract from the back
            self.unassigned.reverse()

    def extract(self):
        if not self.unassigned:
            pass #print "Warning, extracting from empty unassigned list"
            return None
        if self._select == 'random':
            i = random.randint(0,len(self.unassigned)-1)
            nxtvar = self.unassigned[i]
            self.unassigned[i] = self.unassigned[-1]
            self.unassigned.pop()
            return nxtvar
        if self._select == 'fixed':
            return self.unassigned.pop()
        if self._select == 'mrv':
            nxtvar = min(self.unassigned, key=lambda v: v.curDomainSize())
            self.unassigned.remove(nxtvar)
            return nxtvar

    def empty(self):
        return len(self.unassigned) == 0

    def insert(self, var):
        if not var in self.csp.variables():
            pass #print "Error, trying to insert variable {} in unassigned that is not in the CSP problem".format(var.name())
        else:
            self.unassigned.append(var)

def bt_search(algo, csp, variableHeuristic, allSolutions, trace):
    '''Main interface routine for calling different forms of backtracking search
       algorithm is one of ['BT', 'FC', 'GAC']
       csp is a CSP object specifying the csp problem to solve
       variableHeuristic is one of ['random', 'fixed', 'mrv']
       allSolutions True or False. True means we want to find all solutions.
       trace True of False. True means turn on tracing of the algorithm

       bt_search returns a list of solutions. Each solution is itself a list
       of pairs (var, value). Where var is a Variable object, and value is
       a value from its domain.
    '''
    varHeuristics = ['random', 'fixed', 'mrv']
    algorithms = ['BT', 'FC', 'GAC']

    #statistics
    bt_search.nodesExplored = 0

    if variableHeuristic not in varHeuristics:
        pass #print "Error. Unknown variable heursitics {}. Must be one of {}.".format(
            #variableHeuristic, varHeuristics)
    if algo not in algorithms:
        pass #print "Error. Unknown algorithm heursitics {}. Must be one of {}.".format(
            #algo, algorithms)

    uv = UnassignedVars(variableHeuristic,csp)
    Variable.clearUndoDict()
    for v in csp.variables():
        v.reset()
    if algo == 'BT':
         solutions = BT(uv, csp, allSolutions, trace)
    elif algo == 'FC':
        for cnstr in csp.constraints():
            if cnstr.arity() == 1:
                FCCheck(cnstr, None, None)  #FC with unary constraints at the root
        solutions = FC(uv, csp, allSolutions, trace)
    elif algo == 'GAC':
        GacEnforce(csp.constraints(), csp, None, None) #GAC at the root
        solutions = GAC(uv, csp, allSolutions, trace)

    return solutions, bt_search.nodesExplored

def BT(unAssignedVars, csp, allSolutions, trace):
    '''Backtracking Search. unAssignedVars is the current set of
       unassigned variables.  csp is the csp problem, allSolutions is
       True if you want all solutionss trace if you want some tracing
       of variable assignments tried and constraints failed. Returns
       the set of solutions found.

      To handle finding 'allSolutions', at every stage we collect
      up the solutions returned by the recursive  calls, and
      then return a list of all of them.

      If we are only looking for one solution we stop trying
      further values of the variable currently being tried as
      soon as one of the recursive calls returns some solutions.
    '''
    if unAssignedVars.empty():
        if trace: pass #print "{} Solution Found".format(csp.name())
        soln = []
        # print("len:",len(csp.variables()))
        for v in csp.variables():
            if int(v._name) > 0:
                # print("yes")
                soln.append((v, v.getValue()))
        # print("yes")
        return [soln]  #each call returns a list of solutions found
    bt_search.nodesExplored += 1
    solns = []         #so far we have no solutions recursive calls
    # print(unAssignedVars.unassigned)
    nxtvar = unAssignedVars.extract()
    if trace: pass #print "==>Trying {}".format(nxtvar.name())
    for val in nxtvar.domain():
        if trace: pass #print "==> {} = {}".format(nxtvar.name(), val)
        nxtvar.setValue(val)
        constraintsOK = True
        for cnstr in csp.constraintsOf(nxtvar):
            if cnstr.numUnassigned() == 0:
                if not cnstr.check():
                    constraintsOK = False
                    if trace: pass #print "<==falsified constraint\n"
                    break
        if constraintsOK:
            new_solns = BT(unAssignedVars, csp, allSolutions, trace)
            if new_solns:
                solns.extend(new_solns)
            if len(solns) > 0 and not allSolutions:
                break  #don't bother with other values of nxtvar
                       #as we found a soln.
    nxtvar.unAssign()
    unAssignedVars.insert(nxtvar)
    return solns

def output_to_file(filename, sol, size):
    with open(filename,'r+') as file:
        file.truncate(0)
    f = open(filename, "a")
    # f.write("\n\nExploring:\n")
    rows = []
    count = 0
    for (var,val) in sol:
        if count == 6:
            count = 0
            f.write("\n")
            
        f.write(val) # ends with a new line
        # f.write("\n")
        count += 1

    s_ = {}
    for (var, val) in sol:
        s_[int(var.name())] = val
    for i in range(1, size-1):
        for j in range(1, size-1):
            f.write(s_[(i*size+j)])
        f.write("\n")
    f.write("\n")
    f.close()

def print_solution(s, size):
  s_ = {}
  for (var, val) in s:
    s_[int(var.name())] = val
  for i in range(1, size-1):
    for j in range(1, size-1):
    #   print(s_[-1-(i*size+j)],end="")
        print(s_[(i*size+j)],end="")
    print('')

def count_ship_numbers(solution, size):
    four = 0
    three = 0
    two = 0
    one = 0
    s_ = {}
    for (var, val) in solution:
        s_[int(var.name())] = val
    for i in range(1, size-1):
        for j in range(1, size-1):
            # SSSS
            if j < (size - 3) and s_[(i*size+j)] == "S" and s_[(i*size+j+1)] == "S" and s_[(i*size+j+2)] == "S" and s_[(i*size+j+3)] == "S":
                four += 1
                s_[(i*size+j)] = "<"
                s_[(i*size+j+1 )] ="M"
                s_[(i*size+j+2 )] ="M"
                s_[(i*size+j+3 )] =">"
            elif j < (size - 2) and s_[(i*size+j)] == "S" and s_[(i*size+j+1)] == "S" and s_[(i*size+j+2)] == "S":
                three += 1
                s_[(i*size+j)] = "<"
                s_[(i*size+j+1)] = "M"
                s_[(i*size+j+1)] = ">"
            elif j < (size - 1) and s_[(i*size+j)] == "S" and s_[(i*size+j+1)] == "S":
                two += 1
                s_[(i*size+j)] = "<"
                s_[(i*size+j+1)] = ">"
            if i < (size - 3) and s_[(i*size+j)] == "S" and s_[((i+1)*size+j)] == "S" and s_[((i+2)*size+j)] == "S" and s_[((i+3)*size+j)] == "S":
                four += 1
                s_[((i)*size+j)] == "^"
                s_[((i+1)*size+j)] == "M"
                s_[((i+2)*size+j)] == "M"
                s_[((i+3)*size+j)] == "v"
            elif i < (size - 2) and s_[(i*size+j)] == "S" and s_[((i+1)*size+j)] == "S" and s_[((i+2)*size+j)] == "S":
                three += 1
                s_[((i)*size+j)] == "^"
                s_[((i+1)*size+j)] == "M"
                s_[((i+2)*size+j)] == "v"
            elif i < (size - 1) and s_[(i*size+j)] == "S" and s_[((i+1)*size+j)] == "S":
                two += 1
                s_[((i)*size+j)] == "^"
                s_[((i+1)*size+j)] == "v"
    for i in range(1, size-1):
        for j in range(1, size-1):
            if s_[(i*size+j)] == "S":
                one += 1
    return four, three, two, one


if __name__ == "__main__":
    parser = argparse.ArgumentParser()
    parser.add_argument(
        "--inputfile",
        type=str,
        required=True,
        help="The input file that contains the puzzle."
    )
    parser.add_argument(
        "--outputfile",
        type=str,
        required=True,
        help="The output file that contains the solution."
    )
    
    args = parser.parse_args()

    #parse board and ships info
    file = open(args.inputfile, 'r')
    b = file.read()
    b2 = b.split()
    piece_constraint = b2[2]
    size = len(b2[0])
    size = size + 2
    b3 = []
    b3 += ['0' + b2[0] + '0']
    b3 += ['0' + b2[1] + '0']
    b3 += [b2[2] + ('0' if len(b2[2]) == 3 else '')]
    b3 += ['0' * size]
    for i in range(3, len(b2)):
        b3 += ['0' + b2[i] + '0']
    b3 += ['0' * size]
    board = "\n".join(b3)

    varlist = []
    varn = {}
    conslist = []

    #1/0 variables
    for i in range(0,size):
        for j in range(0, size):
            v = None
            if i == 0 or i == size-1 or j == 0 or j == size-1:
                v = Variable(str(-1-(i*size+j)), [0])
            else:
                v = Variable(str(-1-(i*size+j)), [0,1])
            varlist.append(v)
            varn[str(-1-(i*size+j))] = v

    #make 1/0 variables match board info
    ii = 0
    for i in board.split()[3:]:
        jj = 0
        for j in i:
            if j != '0' and j != '.': # must be ship parts
                conslist.append(TableConstraint('boolean_match', [varn[str(-1-(ii*size+jj))]], [[1]]))
            elif j == '.':
                conslist.append(TableConstraint('boolean_match', [varn[str(-1-(ii*size+jj))]], [[0]]))
            jj += 1
        ii += 1

    #row and column constraints on 1/0 variables
    row_constraint = []
    for i in board.split()[0]:
        row_constraint += [int(i)]

    for row in range(0,size):
        conslist.append(NValuesConstraint('row', [varn[str(-1-(row*size+col))] for col in range(0,size)], [1], row_constraint[row], row_constraint[row]))

    col_constraint = []
    for i in board.split()[1]:
        col_constraint += [int(i)]

    for col in range(0,size):
        conslist.append(NValuesConstraint('col', [varn[str(-1-(col+row*size))] for row in range(0,size)], [1], col_constraint[col], col_constraint[col]))

    #diagonal constraints on 1/0 variables
    for i in range(1, size-1):
        for j in range(1, size-1):
            for k in range(9):
                conslist.append(NValuesConstraint('diag', [varn[str(-1-(i*size+j))], varn[str(-1-((i-1)*size+(j-1)))]], [1], 0, 1))
                conslist.append(NValuesConstraint('diag', [varn[str(-1-(i*size+j))], varn[str(-1-((i-1)*size+(j+1)))]], [1], 0, 1))

    # ./S/</>/v/^/M variables
    # these would be added to the csp as well, before searching,
    # along with other constraints
    for i in range(0, size):
        for j in range(0, size):
            v = Variable(str(i*size+j), ['.', 'S', '<', '^', 'v', 'M', '>'])
            varlist.append(v)
            varn[str(str(i*size+j))] = v
            # connect 1/0 variables to W/S/L/R/B/T/M variables
            # make positive pieces ship part when 1, not ship part when 0
            conslist.append(TableConstraint('connect', [varn[str(-1-(i*size+j))], varn[str(i*size+j)]], [[0,'.'],[1,'S'],[1,'<'],[1,'^'],[1,'v'],[1,'M'],[1,'>']]))
            


    #find all solutions and check which one has right ship #'s
    csp = CSP('battleship', varlist, conslist)

    solutions, num_nodes = bt_search('BT', csp, 'fixed', True, False)
    # print(piece_constraint)
    for i in range(len(solutions)):
        # output_to_file(filename=args.outputfile, sol=solutions[i])
        print_solution(solutions[i], size)
        print("--------------")
        four, three, two, one = count_ship_numbers(solutions[i], size)
        if one == piece_constraint[0] and two == piece_constraint[1] and three == piece_constraint[2] and four == piece_constraint[3]:
            print("Solution Found")
            output_to_file(filename=args.outputfile, sol=solutions[i], size=size)
            break
