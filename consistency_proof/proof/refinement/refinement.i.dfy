include "../../model/types.s.dfy"
include "../../model/tako_spec.i.dfy"
include "../../model/tako.i.dfy"

include "refinement_defns.i.dfy"

include "perform_load_refinement.i.dfy"
include "perform_store_refinement.i.dfy"
include "perform_flush_refinement.i.dfy"
include "perform_rmw_refinement.i.dfy"
include "start_on_miss_refinement.i.dfy"
include "start_on_evict_refinement.i.dfy"
include "start_on_write_back_refinement.i.dfy"
include "end_on_miss_refinement.i.dfy"
include "end_on_evict_refinement.i.dfy"
include "end_on_write_back_refinement.i.dfy"
include "perform_branch_refinement.i.dfy"
include "no_op_refinement.i.dfy"
include "refinement_init_proofs.i.dfy"

// This is the definition of the refinement obligation
abstract module RefinementTheorem {
  import opened RefinementTypes
  import TakoSpec
  import Tako
  import Defns: RefinementDefns
  lemma RefinementInit(c: Tako.Constants, v: Tako.Variables)
    requires Tako.Init(c, v)
    ensures Defns.Inv(c, v)
    ensures TakoSpec.Init(Defns.ConstantsAbstraction(c), Defns.VariablesAbstraction(c, v))

  lemma RefinementNext(c: Tako.Constants, v: Tako.Variables, v': Tako.Variables, evt: RefinementEvent)
    requires Tako.Next(c, v, v', evt)
    requires Defns.Inv(c, v)
    ensures Defns.Inv(c, v')
    ensures TakoSpec.NextRefine(Defns.ConstantsAbstraction(c), Defns.VariablesAbstraction(c, v), Defns.VariablesAbstraction(c, v'), evt) || (Defns.VariablesAbstraction(c, v) == Defns.VariablesAbstraction(c, v') && evt == NoOp)
}

// The RefinementProof module refines the abstract RefinementTheorem module. This means
// that it inherits all its functions and lemmas, along with their pre- and post-conditions.
// In the function/lemmas below, we mention the implied pre- and post-conditions for
// reference, as a comment.

module RefinementProof refines RefinementTheorem {
  import Defns = TakoRefinementDefns
  import opened PerformLoadRefinementProof
  import opened PerformStoreRefinementProof
  import opened PerformFlushRefinementProof
  import opened PerformRMWRefinementProof
  import opened StartOnMissRefinementProof
  import opened StartOnEvictRefinementProof
  import opened StartOnWritebackRefinementProof
  import opened EndOnMissRefinementProof
  import opened EndOnEvictRefinementProof
  import opened EndOnWritebackRefinementProof
  import opened PerformBranchRefinementProof
  import opened NoOpRefinementProof
  import opened RefinementInitProof
  import Program

  lemma RefinementInit(c: Tako.Constants, v: Tako.Variables)
    // requires Tako.Init(c, v)
    // ensures Inv(c, v)
    // ensures TakoSpec.Init(ConstantsAbstraction(c), VariablesAbstraction(c, v))
  {
    InitAbstractionCorrect(c, v);
    InvHoldsInitially(c, v);
  }

  lemma RefinementNext(c: Tako.Constants, v: Tako.Variables, v': Tako.Variables, evt: RefinementEvent)
    // requires Tako.Next(c, v, v', evt)
    // requires Inv(c, v)
    // ensures Inv(c, v')
    // ensures TakoSpec.NextRefine(ConstantsAbstraction(c), VariablesAbstraction(c, v), VariablesAbstraction(c, v'), evt) || (VariablesAbstraction(c, v) == VariablesAbstraction(c, v') && evt == NoOp)
  {
    match evt {
      case NoOp => {
        NoOpRefinement(c, v, v');
      }
      case PerformLoad => {
        PerformLoadRefinement(c, v, v');
      }
      case PerformStore => {
        PerformStoreRefinement(c, v, v');
      }
      case PerformRMW => {
        PerformRMWRefinement(c, v, v');
      }
      case PerformFlush => {
        PerformFlushRefinement(c, v, v');
      }
      case StartOnMiss => {
        StartOnMissRefinement(c, v, v');
      }
      case StartOnEvict => {
        StartOnEvictRefinement(c, v, v');
      }
      case StartOnWriteback => {
        StartOnWritebackRefinement(c, v, v');
      }
      case EndOnMiss => {
        EndOnMissRefinement(c, v, v');
      }
      case EndOnEvict => {
        EndOnEvictRefinement(c, v, v');
      }
      case EndOnWriteback => {
        EndOnWritebackRefinement(c, v, v');
      }
      case PerformBranch => {
        PerformBranchRefinement(c, v, v');
      }
    }
  }
}
