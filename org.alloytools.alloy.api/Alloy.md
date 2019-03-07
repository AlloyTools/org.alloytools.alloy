---
title:	Alloy API Overview
---

The Alloy API is a high level API to use Alloy from Java. Its purpose is to establish an abstract API that
allows different Alloy implementations to create a layered interface between the different parts of Alloy so that each
part can be developed in its own way and have multiple independent implementations. 

For example, Electrumn has added a new keyword to the language and is doing work with different kinds of logic. They
have forked Alloy and therefore they have to maintain everything themselves now. This API could be used to share front
end logic including visualizers. For example, we could share a command line tool. 

This API proposal currently provides an abstraction for the the module, compiler, solvers, solutions, instances, atoms, and relations. These are all
defined in a way that allows for many different implementations. It would be desirable to add an abstraction 
for the AST but this is skipped due to its current complexity.

The model of the Alloy API is split in a core, module part and a solver part. The primary object is the Alloy singleton 
that provides access to the implementations.
```alloy
	module	alloy/api
```


The Alloy object will be obtained via the Java Service Loader. This mechanism keeps the implementation of the interface
anonymous.

```alloy
	one sig Alloy {
		preferences		: Id lone -> File,
		solvers			: some Solver,
		defaultResolver		: DefaultContentResolver,
		workingDirectory	: AbsolutePath
	} {
		all disj s1, s2 : solvers | s1.solverId != s2.solverId
	}
```
The Alloy object provides access to the compiler, the compiler can turn a _content_ (source) into an AlloyModule. 
Since the content can be on the file system, remote, or in a GUI widget there is a need to resolve the relative
paths in Alloy source via an indirection that can be set by the caller. This is provided by the 
_Content Resolver_. Each Alloy has a default resolver that maps the names to the underlying file system.

There are therefore 2 ways to get the compiler.

```alloy
	fun Alloy.getCompiler[resolver : ContentResolver] : Compiler  {none}

	fun Alloy.getCompiler[] : Compiler { 
		this.getCompiler[this.defaultResolver]
	}
```
Applications, visualizers, solvers, etc. frequently have the need to store _preferences_ on the file system. However,
when Alloy gets uninstalled these preferences should be removed. For this reason, the Alloy object maintains 
a private directory stored somewhere in the file system that will automatically be removed when Alloy is uninstalled.
The following method allows the diverse Alloy components to get a directory from the file system that is associated
with Alloy.
```alloy
	fun Alloy.getPreferencesDir[ id : Id ] : lone File {
		this.preferences[ id ]
	}
```
Alloy Solvers will be detected through the _Java Service Loader_. The Service Loader finds implementations of 
an interface by looking at metadata specified by modules. Solvers are abstracted on a pretty high level to allow
for many different implementations.
```alloy
	fun Alloy.getSolver[ id : Id ] : lone Solver {
		(this.solvers <: solverId).id
	}
```

## Content Resolver

In many circumstances it is necessary resolve a _Path_ in the Alloy sources to a _Content_.
A path can be a _RelativePath_ but not all Content comes from the default file system. 
For example, the Alloy application stores modules in its user interface to be able to edit them. 
It would be awkward to always save each tab before compiling. Some modules also are embedded 
in Alloy and have a fixed short path. To handle these cases, a resolver allows the caller to 
handle where the actual content comes from. 
```alloy
	abstract sig ContentResolver {
		resolutions : Path lone -> Content
	}

	fun ContentResolver.resolve[ path : Path ] : lone Content {
		this.resolutions[path]
	}	

	one sig DefaultContentResolver extends ContentResolver {}
```
To specify the complete Java file system is out of scope but we need a few objects that abstract the
file system to be able to reason about the Content Resolver.
```alloy
	abstract sig Path {}
	sig AbsolutePath, RelativePath extends Path {}
	sig Content {}
	sig File {}		
	fun AbsolutePath.resolve[ path : RelativePath ] : AbsolutePath {none}
```
	

## Compiler

The _Alloy Compiler_ can take either a _Content_ as a source or a _Path_ in the file system to a source. In both 
cases the compiler turns the source or file into an _Alloy Module_. 
```alloy
	abstract sig Compiler {
		alloy		: Alloy,
		resolver	: ContentResolver
	}

	fun Compiler.compileSource[ source : Content]  : Module  {none}

	fun Compiler.compile[ path : Path ]  : Module {
		this.compileSource[ this.resolver.resolve[path]]
	}
```

## Module

Compiling a Source returns an _Alloy Module_. An Alloy Module holds the AST. Although it would be a good
idea to expose the AST (this would enable a lot of extra applications) this was deemed too complex for now.

However, based on the AST the Alloy Module provides the _meta model_. This consists of the signatures, the fields,
and the commands.

```alloy
	sig Module {
		moduleId: Id,
		path	: lone Path,
		sigs	: set TSig,
		runs	: some TRun,
		asserts	: set TCheck,
		warnings: set CompilerMessage,
		errors	: set CompilerMessage,
		options	: TCommand -> Id lone -> Option,
		compiler: Compiler,
		valid	: boolean
 	} {
		valid=true => no errors
	}

	sig CompilerMessage {}
```

## Commands 

Each module specifies zero or more _TCommand_. A command is either a _TRun_ or a _TCheck_. When a source 
does not specify a TRun command then the module must provide a default TRun command with appropriate defaults.

```alloy
	abstract sig TCommand {
		name	: Id,
		scopes	: set TScope,
		expects	: Resolution,
		module_	: Module
	} {
		scopes.signature = module_.sigs
	}

	sig TRun extends TCommand {} {
		module_ = runs.this
	}

	sig TCheck extends TCommand {} {
		module_ = asserts.this
	}

	enum Resolution { UNKNOWN, SATISFIED, UNSATISFIED }

```

A command also specifies an _expect_. This is intended for automatic testing, the test code can see if a command is 
expected to provide a solution or not when run.

Each command defines a _scope_. A scope sets the bounds for the solution, for example, it defines the maximum 
number of Int atoms to use. In the API, all atoms (including the Int atoms) are treated identical. 

```alloy
	sig TScope {
		signature	: TSig,
		size		: N,
		exact		: boolean
	}
```

## Options

Options can be specified in the source. An option starts with `--option`. Since this indicates a comment older Alloys
will ignore these options. The rest of the line is an assignment like:

	--option                noOverflow=false

This sets the `noOverflow` option to false. The `--option` prefix was chosen because this is a comment in previous Alloy.

In many cases, especially with automated testing, it is useful to be able to specify options per _command_. Options
can therefore be specified with a _selector_. This is a _globbing_ expression on the command name. For example:

	--option.noOvflw_*      noOverflow=true

        run noOvflw_t1 { ... } 

This will override the earlier option and set the `noOverflow` to `true` for the any command (check or run) that has
a name that starts with `oOvflw_*`. Clearly, options are then selective to the command. 

```alloy
	sig Id {}
	abstract sig Option {}
```

## Signatures

A signature is a set of _TField_. Each field specifies a multicolumn _relation_ and has a name and a parent TSig. 
The parent is always in the first column of the relation.

In Alloy, each column of the relation/field is _typed_ with the types of the atoms it can hold. The type
is not a single TSig since a column can handle different sigs if appropriately defined. This is held in the
_TColumnType_. (##note it is probably more complex that is why it has its own sig.)

```alloy
	sig TSig {
		name	: Id,
		fields	: set TField,
	}

	sig TField {
		name	: Id,
		type	: seq TColumnType
	}

	sig TColumnType {
		sigs	: some TSig
	}
```

*note*: not sure if we need to model the `extends` and `in` relations in the API?
*note*: Daniel remarked we can get rid of TColumnType by just making a TField.type a seq 
of `TSig`. Guess it is just flattening.

## Solving

The _Alloy_ object provides access to the solvers that are available. These solvers can take a command from a module
and find an _Alloy Solution_. Alloy Solvers can be enumerated and requested by name. Each solver can describe itself to a user
interface that then is not required to hard code the used solvers.

A solver is completely abstracted, there is no implied semantics that it is a KodKod solver, uses SAT or whatever. 
It should only be able to provide an _Alloy Solution_ based on a command in a module. 

In the API it is possible to pass an instance that should be used as a lower bound of the solution.

```alloy
	sig Solver {
		solverId	: Id,
		available	: boolean,
		solverType	: SolverType,
	}

	fun Solver.newOptions : AlloyOptions {none}
	fun Solver.solve[ command : TCommand, options : lone AlloyOptions, instance : lone Instance ] : Solution {none}

	enum SolverType { SAT, UNSAT, SMT, OTHER }
```

## Solver Options

Solvers can have options. One of the ambitions of this API is to not create any coupling between the UI or command
line code and the actual installed solvers. For this reason, each solver can provide an _option DTO_. A DTO is
an object that only has fields, no methods. In Java, such an object is easy to reflect upon and it is not hard
to create a simple user interface that edits such an object since there is plenty of type information.

For this reason, a solver can provide a default options object. The User interface can edit this and
then provide the edited object when it needs a solution.

```alloy
	abstract sig AlloyOptions {}
```

## Solution

An Alloy Solver provides an _Alloy Solution_. A solution is _not_ an instance. If a solution
is satisfied it can _provide_ one or more instances on demand. 

```alloy
	sig Solution {
		solver		: Solver,
		options		: AlloyOptions,
		module_		: Module,
		command		: TCommand,
		resolution	: Resolution,
		none_		: set univ,
		stream		: lone Stream	
	} {
		no none_ 
	}

	sig Stream {
		next 		: lone Stream,
		instance 	: Instance
	}
```

## Instance

An instance is an actual set of _atoms_ stored in a set of _IRelation_.

```alloy
	sig Instance {
		solution	: Solution,
		relations	: TField one -> IRelation,
		atoms		: TSig -> IAtom,
		variables	: Id -> Id -> IRelation,
		univ_		: IRelation,
		iden_		: IRelation
	} {
		relations.univ in solution.module_.sigs.fields
	}
```

## Relations

In the end, the instance is encoded in _relations_. An IRelation is a set of _ITuple_.  An ITuple
is an array (seq) of _IAtom_. An atom is an opaque object only used for its identity. Atoms are constant
and reused for an Alloy Solution so that for one solution, atoms can be associcated with a color or location.

```alloy
	sig IRelation {
		solution	: Solution,
		arity		: N,
		size		: N,
		tuples		: set ITuple
	} {
		size = # tuples
		all tuple : tuples | # tuple.atoms = arity
		all disj t1, t2 : tuples | t1.atoms != t2.atoms
		arity < 4 // limit in Alloy
	}

	sig ITuple {
		atoms		: seq IAtom
	}

	fact {
		all t : ITuple | let r = tuples.t {
			one r
			all disj t1, t2 : r.tuples | t1.atoms != t2.atoms
		}
	}

	sig IAtom {
		solution	: Solution,
		sig_		: TSig,
		name		: Id,
		index		: N
	}

	fun IRelation.join[ r : IRelation ] : IRelation {none}
	fun IRelation.product[ r : IRelation ] : IRelation {none}
	fun IRelation.head : IRelation {none}
	fun IRelation.tail : IRelation {none}
	pred IRelation.isScalar {
		size = 1 and arity = 1
	}

```
		
## Housekeeping	

```alloy
	enum boolean { false, true }
	let N = { n : Int | n >= 0}

run show {
	some r : IRelation | r.size > 0 and r.arity > 1
} for 5

```

