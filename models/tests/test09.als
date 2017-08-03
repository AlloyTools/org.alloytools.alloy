module tests/test // Bugpost by Richard Sherman <richard.h.sherman@lmco.com>

sig Domain {
   phenomena : set Phenomena // phenomena this domain controls
   , interface : set Interface // interfaces this domain participates in
}

sig DomainType extends Domain{}

sig Causal, Biddable, Lexical extends DomainType{}

sig Description extends DomainType {
   describes : set Phenomena
}

fact {
   Domain in DomainType
   DomainType in Causal + Biddable + Lexical + Description
}

sig DevDescription {
   refers : set Phenomena
   , constrains : set Phenomena
}
{
   no constrains & refers
   no constrains.domain & refers.domain
}

sig Optative extends DevDescription {}
{
   some constrains
}

sig Indicative extends DevDescription {}
{
   no constrains
}

fact {
    DevDescription in Optative + Indicative
}

sig Interface {
   domain : set Domain,
   phenomena : set Phenomena
}
{
   #(this.@domain) > 1
}

fact {
   all i,j : Interface | disj[i,j] => i.domain != j.domain
}

sig Phenomena {
   domain : Domain
   , interface : lone Interface
   , affects : set Domain
}

fact {
   Domain<: phenomena = ~ (Phenomena <:domain)
   Interface<: phenomena = ~ (Phenomena <: interface)
   Phenomena<: affects = Phenomena<: interface.domain - Phenomena<:domain
}

sig State, Event, Symbolic extends Phenomena {}

sig CausalPhenomena in Phenomena {}

fact {
   Phenomena = State + Event + Symbolic
   CausalPhenomena = State + Event
   Phenomena<: domain.Lexical in Symbolic
}

sig Frame {
   requirement : lone DevDescription
   ,  machine, given, designed : set Domain
   , phenomena : set Phenomena
   , interface : set Interface
   , domain : set Domain
}
{
   disj[machine,given,designed]
   domain =  machine + given + designed
   phenomena = interface.@phenomena + requirement.(refers + constrains)
   phenomena = interface.@phenomena + requirement.(refers + constrains)
}

fact {
  all x:Frame | {
     x.phenomena = x.interface.phenomena + x.requirement.(refers + constrains)
     x.phenomena = x.interface.phenomena + x.requirement.(refers + constrains)
  }
}

fact {
   all r : Optative | lone f : Frame | f.requirement = r
}

sig FrameDomain extends Domain {
    inPhenomena : set Phenomena  // phenomena which affect this domain
   , outPhenomena : set Phenomena // phenomena which affect other domains
   , refPhenomena : set Phenomena // phenomena which are only referenced
}
{
    no phenomena & inPhenomena
    inPhenomena = { p : Phenomena | p.affects = this}
    outPhenomena = { p : this.@phenomena | some p.affects }
    refPhenomena =  phenomena - outPhenomena
}

sig FrameAnalysis extends Frame {
   display, operator, realworld, controlled, workpiece, input, output :set Domain
   , feedback : set Interface
}

fact {
  all f : FrameAnalysis {
   all d : Domain {

       d in f.domain and d in Causal and some d.inPhenomena  & f.phenomena and no d.outPhenomena & f.phenomena
         and some d.phenomena & Symbolic & f.phenomena <=> d in f.display

       d in f.domain and d in Biddable and no d.inPhenomena & f.phenomena and some d.outPhenomena & CausalPhenomena  & f.phenomena <=> d in f.operator

       d in f.domain and d in Causal and no d.inPhenomena & f.phenomena and some d.outPhenomena & CausalPhenomena  & f.phenomena and d !in f.machine <=> d in f.realworld

       d in f.domain and d in Causal and some d.inPhenomena & CausalPhenomena & f.phenomena
          and some (d.inPhenomena.domain & f.machine )
          and d !in f.machine
          <=> d in f.controlled

       d in f.domain and d in Lexical and some d.inPhenomena & f.phenomena and some d.outPhenomena & f.phenomena  <=> d in f.workpiece

       d in f.domain and d in Lexical and no d.inPhenomena & f.phenomena and some d.outPhenomena & Symbolic & f.phenomena <=> d in f.input

       d in f.domain and d in Lexical and some d.inPhenomena & Symbolic & f.phenomena and no d.outPhenomena & f.phenomena <=> d in f.output

    some f.requirement.refers  =>
       f.requirement.constrains in
       f.requirement.refers.domain.^
               ((Domain<: phenomena   & f.domain -> f.phenomena).
                (Phenomena<:interface & f.phenomena -> f.interface).
                (Interface<:domain    & f.interface -> f.domain)).
                (Domain<:phenomena   & f.domain -> f.phenomena)
    }
    all i : Interface {

        i in f.interface and (all d : i.domain  & f.domain| some p :
i.phenomena & f.phenomena | d in p.affects )
           <=> i in f.feedback
    }
  }
}

fact {
   Frame in FrameAnalysis
   Domain in FrameDomain
}

sig ContextDiagram extends Frame{}
{
   no this.@phenomena
}

sig ProblemFrame extends Frame {}
{
   one requirement
}

pred frameOnly
{
   Phenomena in Frame.phenomena
   Domain in Frame.domain
   Interface in Frame.interface
   DevDescription in Frame.requirement
}

pred t1  {
      one ProblemFrame
      #Domain = 2
      one f : Frame | one r:  f.requirement | one r.refers
      #Frame = 1
      #Phenomena = 3
      #Interface = 1
      #Optative = 1
      #DevDescription = 1
}

run t1 for 4 expect 0
