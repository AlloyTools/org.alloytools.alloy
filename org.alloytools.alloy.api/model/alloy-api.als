---
---

# A specification of the structure of Alloy

This document specifies a proposed Alloy API. It is reflected in Java in the 
`org.alloytools.alloy.api` project.

## Prelimenaries

The following sigs are used for their identity only.

```alloy
sig Name, Path, Source, Option, Value, Id {}
enum boolean { true, false }
```

## Alloy

The Alloy signature is the top level point of access. To allow multiple implementations,
there is an indirect binding to an implementation via the Java services model.

The Alloy object provides access to the installed _solvers_ and the _compiler_.

For now, a single compiler is assumed. However, it might be interesting to support
multiple compilers. However, this will require an expansion of this API since it
then must define the AST in detail. An aspect that this API skimps on.

A compiler compiles a source string/file to an _Alloy Module_. A _solver_ can then take a
_command_ from this module and create an _Alloy Solution_. A solution can then have
zero or more Alloy Instances with differnet values for this solution.

```alloy
one sig Alloy {
	solvers 	: Id -> AlloySolver,
	compiler 	: AlloyCompiler,
	factories 	: set AlloySolverFactory		
}

```

## Compiler

A compiler needs to be able to resolve path names to source content. Since 
some content can reside in a user interface component it is necessary to have
a component that can resolve a path name to the content, this is the Source Resolver.

```alloy
sig AlloyCompiler {
	resolver	: SourceResolver,
}

sig SourceResolver {
	content	: Path -> Source
}

```

## Modules

A compiler transforms one or more sources int a _module_. A module can refer to other
modules via the `open` statement. A module provides signatures and commands.

```alloy
sig AlloyModule {
	path	: lone Path,
	compiler: AlloyCompiler,
	sigs	: set TSig,
	runs	: set TRun,
	checks 	: set TCheck,
	options	: Option -> Value
}
```

Signatures in alloy are like classes. A signature has a name and groups a 
set of _fields_. A field is a relation where each column is typed. In this
case a type is a set of signatures.

```alloy
sig TSig  {
	name		: Name,
	fields		: set TField,	
}

sig TField {
	type		: seq TColumnType
}

sig TColumnType	{
	signatures	: set TSig,
}
```

## Commands

Each Alloy Module has one or more commands, where a command is either an assertion (`check`)
or a `run` command. A command provides a root for the solver as well as a limit of how
many atoms a solution can make of different types. It also provides an _expects_ which 
indicates if a solution is expected to be satisfied.

```alloy
abstract sig TCommand {
	name	: Name,
	scopes 	: set TScope,
	expects	: Expects
	
}
sig TRun, TCheck extends TCommand {}
sig TScope {
	signature 	: TSig,
	size		: Int,
	exact		: boolean
}
```

## Solvers

Alloy Solvers are _plugged in_ the application. The creation of a solver is indirectly
because not all solvers can run on all platforms. This is the Alloy Solver Factory.

Solvers have a specific type, reflected in the SolverType.

```alloy
enum SolverType {SAT, UNSAT, SMT, OTHER}

sig AlloySolver {
	type		: SolverType,
	id		: Id,	
	name		: Name,
	available	: boolean
}

sig AlloySolverFactory {
	solvers	: set AlloySolver
}
```
## Solutions

Each module has one or more commands. A command can be _solved_ with a solver, providing a 
solution. A solution can then be satisfied or not. Solutions do not provide values yet, to get
the values of a solution _instances_ can be retrieved from a satisfied solution.

Each command has a scope that specifies information how many instances of each signature
can be used.

```alloy
sig AlloySolution {
	satisfied	: boolean,
        command 	: TCommand,
	module_		: AlloyModule,
	solver		: AlloySolver,
	none_		: ITupleSet,
}

enum Expects {
	UNKNOWN, SATISFIED, UNSATISFIED
}

```

### Instances

Once a satisfied solution is found, it is possible to iterate over the _instances_
of the solution. An instance contains values that satisfy the constraints in the original
source. Each instance generated will be a different set of atoms.

All values are represented as ITuple Sets. 

```alloy
sig AlloyInstance {
	solution 	: AlloySolution,
	fields		: TField -> ITupleSet,
	variables 	: Name -> Name -> ITupleSet,
	universe	: ITupleSet,
	identity	: ITupleSet,
}

sig IAtom {
	solution  : AlloySolution,
	signature : TSig,
}

sig ITuple {
	solution : AlloySolution,
	atoms : seq IAtom
}

sig ITupleSet {
	solution : AlloySolution,
	tuples	: set ITuple	
}


