module tests/test // Bugpost by C. M. Sperberg-McQueen <cmsmcq@acm.org>
open util/relation as R

// Some primitive, unanalysed signatures:
// names, documents, resources
sig Name {}
sig XMLDoc {}
sig nonXML {}

// Any pipeline component has inputs and outputs.
abstract sig Component {
  ins: Name -> lone XMLDoc,
  outs: Name -> lone XMLDoc
}{
  // The names of input and output ports are disjoint.
  no dom[ins] & dom[outs]

  // No document is simultaneously an input and an output
  // for the same component.
  no ran[ins] & ran[outs]
}
// Steps (atomic components) have no further internal
// structure, just inputs and outputs.
abstract sig Step extends Component {}
// Constructs (compound components), however, have
// nested components
abstract sig Construct extends Component {
  components: set Component,
  descendants: set Component
}{
  descendants = ran[^@components]
  descendants = ran[^@components]
}

sig Pipeline extends Construct {}

sig Identity extends Step {}
sig XSLT extends Step {}
sig Validate extends Step {}{
  some document, schema : Name
      | some X1, X2 : XMLDoc
      | disj[document, schema]
         // N.B. the Names are disjoint, not necessarily the documents
         and ins = ( document -> X1 + schema -> X2 )

  some result : Name
      | some X : XMLDoc
      | outs = ( result -> X )
}

sig XInclude extends Step {}{
  some document : Name
      | some X : XMLDoc
         | ins = ( document -> X )

  some result : Name
      | some X : XMLDoc
         | outs = ( result -> X )
}

sig Serialize extends Step {}
sig Parse extends Step {}
sig Load extends Step {}
sig Store extends Step {}
sig ExtensionStep extends Step {
  type : Name
}

pred show (p: Pipeline) {
  some p.ins
  some p.outs
  Component = p + p.^components
}

run show for 3 but 1 Pipeline expect 1
