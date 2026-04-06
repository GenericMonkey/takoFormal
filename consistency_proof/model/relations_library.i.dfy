module Library {
  ghost function dom<T>(rel: set<(T, T)>) : set<T> {
    set a | a in rel :: a.0
  }

  ghost function range<T>(rel: set<(T, T)>) : set<T> {
    set a | a in rel :: a.1
  }

  ghost function restriction<T>(rel: set<(T, T)>, res: set<T>) : set<(T, T)> {
    set e1 : T, e2 : T | (e1, e2) in rel && e1 in res && e2 in res :: (e1, e2)
  }

  ghost function compose<T(!new)>(rel1: set<(T, T)>, rel2: set<(T, T)>) : set<(T, T)> {
    // set e1 : T, e2 : T, e3 : T | (e1, e2) in rel1 && (e2, e3) in rel2 :: (e1, e3)
    set a, b | a in rel1 && b in rel2 && a.1 == b.0 :: (a.0, b.1)
  }

  ghost function iden<T(!new)>(s: set<T>) : set<(T, T)> {
    set e | e in s :: (e, e)
  }

  ghost function prod<T(!new)>(s1: set<T>, s2: set<T>) : set<(T,T)> {
    set e1 : T, e2 : T | e1 in s1 && e2 in s2 :: (e1, e2)
  }

  ghost function intersection<T>(s1: set<T>, s2: set<T>) : set<T> {
    set e | e in s1 && e in s2 :: e
  }

  ghost function inverse<T>(rel: set<(T, T)>) : set<(T, T)> {
    set e | e in rel :: (e.1, e.0)
  }

  ghost opaque function trans_closure<T(!new)>(rel: set<(T, T)>) : (res : set<(T, T)>)

  {
    // if |rel| == 0 then {} else
    //   var len := |dom(rel) + range(rel)| - 1;
    //   var x :| x in rel;
    //   assert x.0 in dom(rel);
    //   trans_closure_helper(rel, len)
    trans_closure_helper(rel, |rel|)
  }

  ghost function trans_closure_helper<T(!new)>(rel: set<(T, T)>, card: nat) : (res : set<(T, T)>)
    requires card <= |rel|
    decreases card
  {
    compose_n(rel, |rel| - card) +
    (
      if card == 0 then {}
      else trans_closure_helper(rel, card - 1)
    )
  }


  ghost opaque function compose_n<T(!new)>(rel: set<(T, T)>, n: nat) : set<(T, T)>
  {
    match n {
      case 0 => {}
      case 1 => rel
      case _ => compose(rel, compose_n(rel, n - 1))
    }
  }


  ghost predicate irreflexive<T(!new)>(rel: set<(T, T)>) {
    forall e1 : T, e2: T | (e1, e2) in rel :: e1 != e2
  }

  ghost predicate complete<T>(rel: set<(T, T)>, events: set<T>) {
    forall e1 : T, e2: T | e1 in events && e2 in events && e1 != e2 :: (e1, e2) in rel || (e2, e1) in rel
  }

  ghost predicate stricttotalorder<T(!new)>(rel: set<(T, T)>, events: set<T>) {
    && irreflexive(rel)
    && transitive(rel)
    && complete(rel, events)
  }


  ghost predicate reflexive<T>(rel: set<(T, T)>) {
    forall e : T | e in dom(rel) :: (e, e) in rel
  }

  ghost predicate symmetric<T(!new)>(rel: set<(T, T)>) {
    forall e1 : T, e2: T | (e1, e2) in rel :: (e2, e1) in rel
  }

  ghost predicate transitive<T(!new)>(rel: set<(T, T)>) {
    forall e1, e2, e3 : T | (e1, e2) in rel && (e2, e3) in rel :: (e1, e3) in rel
  }

  ghost predicate equivalence<T(!new)>(rel: set<(T, T)>) {
    && reflexive(rel)
    && symmetric(rel)
    && transitive(rel)
  }


  lemma IrreflexiveMonotonicity<T(!new)>(e: set<T>, e_sub: set<T>, rel: set<(T, T)>)
    requires e_sub <= e
    requires irreflexive(rel)
    requires forall e1, e2 : T | (e1, e2) in rel :: e1 in e && e2 in e
    ensures irreflexive(restriction(rel, e_sub))
  {
  }

  lemma IrreflexiveMonotonicityStrong<T(!new)>(rel: set<(T, T)>, rel_sub: set<(T, T)>)
    requires rel_sub <= rel
    requires irreflexive(rel)
    ensures irreflexive(rel_sub)
  {
  }

  lemma StrictTotalOrderMonotonicity<T(!new)>(e: set<T>, e_sub: set<T>, rel: set<(T, T)>)
    requires e_sub <= e
    requires stricttotalorder(rel, e)
    requires forall e1, e2 : T | (e1, e2) in rel :: e1 in e && e2 in e
    ensures stricttotalorder(restriction(rel, e_sub), e_sub)
  {
  }

  lemma CompositionAssoc<T(!new)>(rel1: set<(T, T)>, rel2: set<(T, T)>, rel3: set<(T, T)>)
    ensures compose(compose(rel1, rel2), rel3) == compose(rel1, compose(rel2, rel3))
  {
  }

  lemma TransClosureTransitive<T(!new)>(rel: set<(T, T)>)
    ensures transitive(trans_closure(rel))
  {
    forall e1, e2, e3 : T | (e1, e2) in trans_closure(rel) && (e2, e3) in trans_closure(rel)
      ensures (e1, e3) in trans_closure(rel)
    {
      var n := TransClosureMembership(rel, e1, e2);
      var m := TransClosureMembership(rel, e2, e3);
      // assert (exists n: nat :: (e1, e2) in compose_n(rel, n));
      // var n : nat :| n <= |rel| && (e1, e2) in compose_n(rel, n) && not_in_lower(rel, n, e1, e2);
      // var m: nat :| m <= |rel| && (e2, e3) in compose_n(rel, m) && not_in_lower(rel, m, e2, e3);
      if n + m <= |rel| {
        CombiningTwoSmallChainsWorks(rel, n, m, e1, e2, e3);
      } else {
        CombiningTwoLongerChainsWorks(rel, n, m, e1, e2, e3);
      }

    }
  }

  lemma TransClosureSuperSet<T(!new)>(rel: set<(T, T)>)
    ensures rel <= trans_closure(rel)
  {
    reveal trans_closure;
    if |rel| == 0 {
      assert rel <= trans_closure(rel);
    } else {
      reveal compose_n;
      assert trans_closure(rel) == trans_closure_helper(rel, |rel|);
    }

  }

  lemma DomUnionCommute<T(!new)>(rel1: set<(T, T)>, rel2: set<(T, T)>)
    ensures dom(rel1 + rel2) == dom(rel1) + dom(rel2)
  {
  }

  ghost predicate AllPairsIdentity<T(!new)>(rel: set<(T, T)>, e: T)
  {
    forall e2 : T | (e, e2) in rel :: e == e2
  }

  lemma TransClosurePreservesAllPairsIdentity<T(!new)>(rel: set<(T, T)>, e: T)
    requires AllPairsIdentity(rel, e)
    ensures AllPairsIdentity(trans_closure(rel), e)
  {
    forall e2 : T | (e, e2) in trans_closure(rel)
      ensures e == e2
    {
      var n := TransClosureMembership(rel, e, e2);
      var s := InComposeNMinMeansUniqueNSequenceExists(rel, n, e, e2);
      assert n == 1 by {
        assert n != 0 by {
          reveal compose_n;
        }
        if n > 1 {
          reveal chain;
          var head := s[0];
          var tail := s[1..];
          assert head.1 == e;
          assert tail[0].0 == e;
          assert chain(tail, rel, n - 1, e, e2);
          ChainNMeansInComposeN(rel, n - 1, e, e2, tail);
          reveal not_in_lower;
          assert false;
        }
      }
      assert s == [(e, e2)] by {
        reveal chain;
      }
      assert (e, e2) in rel by {
        reveal chain;
      }
      assert e2 == e;
    }
  }

  lemma TransClosureExtension<T(!new)>(rel: set<(T, T)>, ext: set<(T, T)>, e: T)
    requires !(e in dom(rel))
    requires (e in dom(ext)) ==> AllPairsIdentity(ext, e)
    requires range(ext) <= {e}
    ensures range(trans_closure(rel + ext) - trans_closure(rel)) <= {e}
  {
    reveal compose_n;
    forall e1, e2 : T | (e1, e2) in (trans_closure(rel + ext) - trans_closure(rel))
      ensures e2 == e
    {
      assert (e1, e2) in trans_closure(rel + ext);
      assert !((e1, e2) in trans_closure(rel));
      var n := TransClosureMembership(rel + ext, e1, e2);
      var s := InComposeNMinMeansUniqueNSequenceExists(rel + ext, n, e1, e2);
      assert exists i : nat :: i < |s| && s[i] in ext && !(s[i] in rel) by {
        assert forall i : nat | i < |s| :: s[i] in rel || s[i] in ext by {
          reveal chain;
        }
        if forall i : nat | i < |s| :: s[i] in rel {
          assert chain(s, rel, n, e1, e2) by {
            reveal chain;
          }
          assert n <= |rel| by {
            assert |s| == n by {
              reveal chain;
            }
            assert unique(s);
            var s_set := UniqueChainToSet(s);
            assert s_set <= rel;
            LemmaSubsetSize(s_set, rel);
            assert |s_set| <= |rel|;
          }
          ChainNMeansInComposeN(rel, n, e1, e2, s);
          InComposeNMeansInTransClosure(rel, n, e1, e2);
          assert false;
        }
      }
      var i : nat :| i < |s| && s[i] in ext && !(s[i] in rel);
      var last := s[i];
      assert last.1 == e by {
        assert last.1 in range(ext);
      }
      assert i == |s| - 1 by {
        if i < |s| - 1 {
          var next := s[i + 1];
          assert next in rel + ext by {
            reveal chain;
          }
          assert next.0 == e by { reveal chain; }
          assert next.1 == e;// by { reveal AllPairsIdentity; }
          var remove_dup := s[..i + 1] + s[i + 2..];
          assert chain(remove_dup, rel + ext, n - 1, e1, e2) by {
            reveal chain;
          }
          if n > 1 {
            ChainNMeansInComposeN(rel + ext, n - 1, e1, e2, remove_dup);
            reveal not_in_lower;
            assert false;
          } else if n == 1 {
            assert n == |s| by {
              reveal chain;
            }
            assert false;
          }
        }
      }
      assert last.1 == e2 by {
        reveal chain;
      }
    }

  }

  lemma CompositionExtension<T(!new)>(rel1': set<(T, T)>, rel1: set<(T, T)>, rel2': set<(T, T)>, rel2: set<(T, T)>, e: T)
    requires range(rel1' - rel1) <= {e}
    requires (e in dom(rel2')) ==> AllPairsIdentity(rel2', e)
    requires range(rel2' - rel2) <= {e}
    ensures range(compose(rel1', rel2') - compose(rel1, rel2)) <= {e}
  {
    forall e1, e2 : T | (e1, e2) in compose(rel1', rel2') - compose(rel1, rel2)
      ensures e2 == e
    {
      assert (e1, e2) in compose(rel1', rel2');
      assert !((e1, e2) in compose(rel1, rel2));
      var emid :| (e1, emid) in rel1' && (emid, e2) in rel2';
      if emid != e {
        assert emid != e;
        assert (e1, emid) in rel1 by {
          assert !(emid in range(rel1' - rel1));
          if !((e1, emid) in rel1) {
            assert (e1, emid) in rel1' - rel1;
            assert false;
          }
        }
        if e2 != e {
          assert (emid, e2) in rel2 by {
            if !((emid, e2) in rel2) {
              assert (emid, e2) in rel2' - rel2;
              assert e2 in range(rel2' - rel2);
              assert false;
            }
          }
          assert false;
        }
      }
    }

  }

  lemma TransClosureMonotonic<T(!new)>(rel: set<(T, T)>, rel': set<(T, T)>)
    requires rel <= rel'
    ensures trans_closure(rel) <= trans_closure(rel')
  {
    reveal compose_n;
    forall p : (T, T) | p in trans_closure(rel)
      ensures p in trans_closure(rel')
    {
      var e1 := p.0;
      var e2 := p.1;
      var n := TransClosureMembership(rel, e1, e2);
      var s := InComposeNMinMeansUniqueNSequenceExists(rel, n, e1, e2);
      assert chain(s, rel', n, e1, e2) by {
        reveal chain;
      }
      ChainNMeansInComposeN(rel', n, e1, e2, s);
      assert n <= |rel|;
      LemmaSubsetSize(rel, rel');
      InComposeNMeansInTransClosure(rel', n, e1, e2);
    }
  }

  lemma UnionWithDifferenceIsSameAsUnion<T>(A: set<T>, B: set<T>)
    requires A <= B
    ensures A + (B - A) == B
  {
  }

  lemma CompositionMonotonic<T(!new)>(A: set<(T, T)>, B: set<(T, T)>, A': set<(T, T)>, B': set<(T, T)>)
    requires A <= A'
    requires B <= B'
    ensures compose(A, B) <= compose(A', B')
  {
  }

  lemma CompositionDomRange<T(!new)>(rel1: set<(T, T)>, rel2: set<(T, T)>)
    ensures dom(compose(rel1, rel2)) <= dom(rel1)
    ensures range(compose(rel1, rel2)) <= range(rel2)
  {
  }

  lemma IrreflexivePreservedUnderNewExtension<T(!new)>(rel: set<(T, T)>, ext: set<(T, T)>, e: T)
    requires irreflexive(rel)
    requires !(e in dom(rel))
    requires !(e in range(rel))
    requires !(e in dom(ext))
    requires range(ext) <= {e}
    ensures irreflexive(rel + ext)
  {
    if p :| p in rel + ext && p.0 == p.1 {
      if p.0 == e {
        assert p in ext;
        // assert p.0 in dom(ext);
        assert false;
      } else {
        assert p in rel by {
          if p in ext {
            assert p.1 in range(ext);
            assert false;
          }
        }
        assert false;
      }
    }
  }

  lemma IrreflexivePreservedUnderUnion<T(!new)>(rel: set<(T, T)>, ext: set<(T, T)>)
    requires irreflexive(rel)
    requires irreflexive(ext)
    ensures irreflexive(rel + ext)
  {
  }

  lemma TransClosureDomainRange<T(!new)>(rel: set<(T, T)>)
    ensures dom(trans_closure(rel)) == dom(rel)
    ensures range(trans_closure(rel)) == range(rel)
  {
    TransClosureSuperSet(rel);
    forall p : (T, T) | p in trans_closure(rel)
      ensures p.0 in dom(rel)
      ensures p.1 in range(rel)
    {
      var n := TransClosureMembership(rel, p.0, p.1);
      var s := InComposeNMinMeansUniqueNSequenceExists(rel, n, p.0, p.1);
      assert p.0 in dom(rel) by { reveal chain; }
      assert p.1 in range(rel) by { reveal chain; }
    }
  }

  ////////////////////////////////////////////////////////////////////////
  // Properties to help with the proof
  ////////////////////////////////////////////////////////////////////////



  ghost opaque predicate not_in_lower<T(!new)>(rel: set<(T, T)>, n: nat, e1: T, e2: T) {
    forall k : nat | k < n :: !((e1, e2) in compose_n(rel, k))
  }

  ghost opaque predicate unique<T>(s: seq<T>) {
    && (forall i: nat, j: nat | i < |s| && j < |s| :: i != j ==> s[i] != s[j])
  }


  ghost predicate exists_match<T>(d: set<nat>, s1: seq<(T, T)>, s2: seq<(T, T)>) {
    && (forall i: nat | i in d :: i < |s1| && exists j: nat | j < |s2| :: s1[i] == s2[j])
  }

  ghost opaque predicate chain<T>(s: seq<(T, T)>, rel: set<(T, T)>, n: nat, e1: T, e2: T)
  {
    && n > 0
    && |s| == n
    && (forall i: nat | i < |s| :: s[i] in rel)
    && (forall i: nat | i < |s| - 1 :: s[i].1 == s[i + 1].0)
    && s[0].0 == e1
    && s[|s| - 1].1 == e2
  }

  // Chain Properties

  lemma SingletonChain<T>(rel: set<(T, T)>, e1: T, e2: T)
    requires (e1, e2) in rel
    ensures chain([(e1, e2)], rel, 1, e1, e2)
  {
    reveal chain;
  }

  lemma SubChainIsChain<T>(s: seq<(T, T)>, rel: set<(T, T)>, n: nat, e1: T, e2: T, m: nat)
    requires |s| == n
    requires chain(s, rel, n, e1, e2)
    requires m < n
    ensures chain(s[m..], rel, n - m, s[m].0, e2)
  {
    reveal chain;
    assert s[m..][0].0 == s[m].0;
  }

  lemma CombinedChainIsChain<T>(s1 : seq<(T,T)>, s2: seq<(T,T)>, rel: set<(T, T)>, n1: nat, n2: nat, e1: T, e2: T, e3: T)
    requires chain(s1, rel, n1, e1, e2)
    requires chain(s2, rel, n2, e2, e3)
    ensures chain(s1 + s2, rel, n1 + n2, e1, e3)
  {
    reveal chain;
  }

  // Unique Properties

  lemma UniqueWithNewElemIsUnique<T>(s: seq<T>, e: T)
    requires unique(s)
    requires !(e in s)
    ensures unique([e] + s)
  {
    reveal unique;
  }

  // NotInLower Properties

  lemma NotInLowerSubChain<T(!new)>(rel: set<(T,T)>, n: nat, e1: T, e2: T, emid: T)
    requires n > 1
    requires (e1, e2) in compose_n(rel, n)
    requires (e1, emid) in rel && (emid, e2) in compose_n(rel, n - 1)
    requires not_in_lower(rel, n, e1, e2)
    ensures not_in_lower(rel, n - 1, emid, e2)
  {
    reveal compose_n;
    assert not_in_lower(rel, n - 1, emid, e2) by {
      // show by contradiction that emid ... e2 couldn't exist in less than n - 1 steps
      // if it did, then we would have a contradiction with the assumption that n is the minimum
      if !not_in_lower(rel, n - 1, emid, e2) {
        assert exists m : nat :: m < n - 1 && (emid, e2) in compose_n(rel, m) by {
          reveal not_in_lower;
        }
        var m : nat :| m < n - 1 && (emid, e2) in compose_n(rel, m);
        assert (e1, e2) in compose_n(rel, m + 1);
        assert m + 1 < n;
        assert false by {
          reveal not_in_lower;
        }
      }
    }

  }
  lemma NotInLowerAndNotInComposeNMeansNotInLower<T(!new)>(rel: set<(T, T)>, n: nat, e1: T, e2: T)
    requires not_in_lower(rel, n, e1, e2)
    requires !((e1, e2) in compose_n(rel, n))
    ensures not_in_lower(rel, n + 1, e1, e2)
  {
    reveal not_in_lower;
  }

  lemma AddingNewToUniqueIsUnique<T(!new)>(rel: set<(T,T)>, n: nat, e1: T, e2: T, emid: T, s: seq<(T, T)>, s': seq<(T, T)>)
    requires n > 1
    requires not_in_lower(rel, n, e1, e2)
    requires chain(s, rel, n - 1, emid, e2)
    requires unique(s)
    requires s' == [(e1, emid)] + s
    ensures unique(s')
  {
    assert unique(s') by {
      assert !((e1, emid) in s) by {
        if (e1, emid) in s {
          var i : nat :| i < |s| && s[i] == (e1, emid);
          assert i != 0 by {
            if i == 0 {
              assert e1 == emid by { reveal chain; }
              if |s| == 1 {
                assert e1 == e2 by { reveal chain; }
                assert chain([(e1, e2)], rel, 1, e1, e2) by { reveal chain; }
                ChainNMeansInComposeN(rel, 1, e1, e2, [(e1, e2)]);
                assert false by {
                  reveal not_in_lower;
                  assert (e1, e2) in compose_n(rel, 1);
                }
              }
              assert chain(s[1..], rel, |s| - 1, e1, e2) by {
                reveal chain;
              }
              ChainNMeansInComposeN(rel, |s| - 1, e1, e2, s[1..]);
              assert false by {
                reveal not_in_lower;
                assert (e1, e2) in compose_n(rel, |s| - 1);
                assert |s| - 1 < n by {
                  reveal chain;
                }
              }
            }
          }
          assert chain(s[i..], rel, |s| - i, e1, e2) by {
            reveal chain;
          }
          ChainNMeansInComposeN(rel, |s| - i, e1, e2, s[i..]);
          assert false by {
            reveal not_in_lower;
            assert |s| - i < n by { reveal chain; }
            assert (e1, e2) in compose_n(rel, |s| - i);
          }
        }
      }
      UniqueWithNewElemIsUnique(s, (e1, emid));
    }
  }

  ////////////////////////////////////////////////////////////////////////
  // Subset Lemmas from Std Sets Library
  ////////////////////////////////////////////////////////////////////////

  /* If x is a subset of y, then the size of x is less than or equal to the
  size of y. */
  lemma LemmaSubsetSize<T>(x: set<T>, y: set<T>)
    ensures x < y ==> |x| < |y|
    ensures x <= y ==> |x| <= |y|
  {
    if x != {} {
      var e :| e in x;
      LemmaSubsetSize(x - {e}, y - {e});
    }
  }

  /* Construct a set with all integers in the range [a, b). */
  opaque function SetRange(a: int, b: int): (s: set<int>)
    requires a <= b
    ensures forall i {:trigger i in s} :: a <= i < b <==> i in s
    ensures |s| == b - a
    decreases b - a
  {
    if a == b then {} else {a} + SetRange(a + 1, b)
  }

  /* If a set solely contains integers in the range [a, b), then its size is
  bounded by b - a. */
  lemma LemmaBoundedSetSize(x: set<int>, a: int, b: int)
    requires forall i {:trigger i in x} :: i in x ==> a < i < b
    requires a < b
    ensures |x| < b - a
  {
    var range := SetRange(a, b);
    forall e {:trigger e in range}{:trigger e in x} | e in x
      ensures e in range
    {
    }
    assert a in SetRange(a, b);
    assert x < range;
    LemmaSubsetSize(x, range);
  }

  // Additional Set Properties

  lemma ExistsSmallIndexEntry(s : set<nat>, n: nat)
    requires 1 <= |s| <= n
    requires forall i: nat | i in s :: i < n
    ensures exists i : nat :: i in s && i <= n - |s|
  {
    if forall i: nat | i in s :: i > n - |s| {
      var x := SetRange(n - |s| + 1, n);
      LemmaBoundedSetSize(x, n - |s|, n);
      assert |x| < |s|;
      assert s <= x;
      LemmaSubsetSize(s, x);
      assert |s| <= |x|;
      assert false;
    }
  }

  lemma IndexSetFromSet<T(!new)>(s: set<(T, T)>, s_seq: seq<(T, T)>) returns (res: set<nat>)
    requires |s_seq| > 0
    requires forall e | e in s :: (exists i : nat :: i < |s_seq| && s_seq[i] == e)
    ensures |res| == |s|
    ensures forall i : nat | i in res :: i < |s_seq| && s_seq[i] in s
  {
    if s == {} {
      return {};
    } else {
      var e :| e in s;
      var i : nat :| i < |s_seq| && s_seq[i] == e;
      var rest := IndexSetFromSet(s - {e}, s_seq);
      return {i} + rest;
    }
  }

  lemma DuplicatesExistInSetOverlap<T>(s1: set<T>, s2: set<T>, s : set<T>) returns (d: set<T>)
    requires s1 <= s
    requires s2 <= s
    requires |s1| + |s2| > |s|
    decreases |s1| + |s2| - |s|
    ensures |d| == |s1| + |s2| - |s|
    ensures d <= s1
    ensures d <= s2
  {
    assert (exists e : T :: e in s1 && e in s2) by {
      if forall e : T | e in s1 :: !(e in s2) {
        assert |s1 + s2| == |s1| + |s2|;
        assert s1 + s2 <= s;
        LemmaSubsetSize(s1 + s2, s);
        assert false;
      }
    }
    var e : T :| e in s1 && e in s2;
    if |s1| + |s2| - |s| == 1 {
      return {e};
    } else {
      var rest := DuplicatesExistInSetOverlap(s1, s2 - {e}, s);
      return {e} + rest;
    }

  }

  ghost opaque function UniqueChainToSet<T(!new)>(s: seq<(T, T)>) : (res: set<(T,T)>)
    requires unique(s)
    ensures |s| == |res|
    ensures (forall e :: e in res <==> e in s)
  {
    var res :=
      if |s| == 0 then
        {}
      else
        {s[0]} +
        (
          assert unique(s[1..]) by { reveal unique; }
          var rec := UniqueChainToSet(s[1..]);
          assert !(s[0] in rec) by {
            reveal unique;
          }
          rec
        );
    res
  }

  lemma CombiningTwoSmallChainsWorks<T(!new)>(rel: set<(T,T)>, n: nat, m: nat, e1: T, e2: T, e3: T)
    requires n <= |rel|
    requires (e1, e2) in compose_n(rel, n)
    requires not_in_lower(rel, n, e1, e2)
    requires m <= |rel|
    requires (e2, e3) in compose_n(rel, m)
    requires not_in_lower(rel, m, e2, e3)
    requires m + n <= |rel|
    ensures (e1, e3) in trans_closure(rel)
  {
    reveal compose_n;
    var sn := InComposeNMinMeansUniqueNSequenceExists(rel, n, e1, e2);
    var sm := InComposeNMinMeansUniqueNSequenceExists(rel, m, e2, e3);
    // var sn :| chain(sn, rel, n, e1, e2) && unique(sn);
    // var sm :| chain(sm, rel, m, e2, e3) && unique(sm);
    var s := sn + sm;
    assert chain(s, rel, n + m, e1, e3) by {
      CombinedChainIsChain(sn, sm, rel, n, m, e1, e2, e3);
    }
    ChainNMeansInComposeN(rel, n + m, e1, e3, s);
    InComposeNMeansInTransClosure(rel, n + m, e1, e3);
  }

  lemma CombiningTwoLongerChainsWorks<T(!new)>(rel: set<(T,T)>, n: nat, m: nat, e1: T, e2: T, e3: T)
    requires n <= |rel|
    requires (e1, e2) in compose_n(rel, n)
    requires not_in_lower(rel, n, e1, e2)
    requires m <= |rel|
    requires (e2, e3) in compose_n(rel, m)
    requires not_in_lower(rel, m, e2, e3)
    requires m + n > |rel|
    ensures (e1, e3) in trans_closure(rel)
  {
    var sn := InComposeNMinMeansUniqueNSequenceExists(rel, n, e1, e2);
    var sm := InComposeNMinMeansUniqueNSequenceExists(rel, m, e2, e3);
    // var sn : seq<(T,T)> :| chain(sn, rel, n, e1, e2) && unique(sn);
    // var sm : seq<(T,T)> :| chain(sm, rel, m, e2, e3) && unique(sm);
    assert n == |sn| by {
      reveal chain;
    }
    assert m == |sm| by {
      reveal chain;
    }
    TwoUniqueChainsProduceDuplicates(rel, sn, sm, e1, e2, e2, e3);
    // var dups : set<nat> :| |dups| == n + m - |rel| && (forall i: nat | i in dups :: i < n && exists j: nat | j < m :: sn[i] == sm[j]);
    var dups : set<nat> :| |dups| == n + m - |rel| && exists_match(dups, sn, sm);
    ExistsSmallIndexEntry(dups, n);
    var i : nat :| i in dups && i <= n - |dups|;
    assert i <= |rel| - m;
    var j : nat :| j < m && sn[i] == sm[j];
    CombiningChainsAtAppropriateIndicesInClosure(rel, n, m, sn, sm, e1, e2, e3, i, j);
  }

  lemma CombiningChainsAtAppropriateIndicesInClosure<T(!new)>(rel: set<(T,T)>, n: nat, m: nat, sn: seq<(T,T)>, sm: seq<(T,T)>, e1: T, e2: T, e3: T, i: nat, j: nat)
    requires n <= |rel|
    requires chain(sn, rel, n, e1, e2)
    requires m <= |rel|
    requires (e2, e3) in compose_n(rel, m)
    requires chain(sm, rel, m, e2, e3)
    requires m + n > |rel|
    requires i < n
    requires i <= |rel| - m
    requires j < m
    requires |sn| == n
    requires |sm| == m
    requires sn[i] == sm[j]
    ensures (e1, e3) in trans_closure(rel)
  {
    if i == 0 {
      assert chain(sm[j..], rel, m - j, e1, e3) by {
        reveal chain;
        assert sn[i].0 == sm[j].0;
        assert sm[j..][0].0 == sm[j].0;
      }
      ChainNMeansInComposeN(rel, m - j, e1, e3, sm[j..]);
      InComposeNMeansInTransClosure(rel, m - j, e1, e3);
    } else {
      assert chain(sn[..i], rel, i, e1, sn[i].0) by {
        reveal chain;
        assert sn[..i][i - 1].1 == sn[i].0;
      }
      assert chain(sm[j..], rel, m - j, sn[i].0, e3) by {
        reveal chain;
        assert sn[i].0 == sm[j].0;
        assert sm[j..][0].0 == sm[j].0;
      }
      CombinedChainIsChain(sn[..i], sm[j..], rel, i, m - j, e1, sn[i].0, e3);
      assert chain(sn[..i] + sm[j..], rel, i + m - j, e1, e3);
      ChainNMeansInComposeN(rel, i + m - j, e1, e3, sn[..i] + sm[j..]);
      InComposeNMeansInTransClosure(rel, i + m - j, e1, e3);
    }
  }

  lemma TwoUniqueChainsProduceDuplicates<T(!new)>(rel: set<(T,T)>, s1: seq<(T,T)>, s2: seq<(T,T)>, e1: T, e2: T, e3: T, e4: T)
    requires unique(s1)
    requires chain(s1, rel, |s1|, e1, e2)
    requires unique(s2)
    requires chain(s2, rel, |s2|, e3, e4)
    requires |s1| + |s2| > |rel|
    ensures exists d: set<nat> ::
      && |d| == |s1| + |s2| - |rel|
      && exists_match(d, s1, s2)
  {
    var s1_set := UniqueChainToSet(s1);
    var s2_set := UniqueChainToSet(s2);
    assert |s1_set| + |s2_set| > |rel|;
    assert s1_set <= rel by {
      reveal chain;
    }
    assert s2_set <= rel by {
      reveal chain;
    }
    var d_set := DuplicatesExistInSetOverlap(s1_set, s2_set, rel);
    var d_idxs := IndexSetFromSet(d_set, s1);
  }

  lemma InComposeNMeansInTransClosure<T(!new)>(rel: set<(T, T)>, n: nat, e1: T, e2: T)
    requires n <= |rel|
    requires (e1, e2) in compose_n(rel, n)
    ensures (e1, e2) in trans_closure(rel)
  {
    reveal trans_closure;
    assert (e1, e2) in trans_closure_helper(rel, |rel| - n);
    TransClosureHelperNested(rel, |rel| - n, |rel|);
  }

  lemma TransClosureHelperNested<T(!new)>(rel: set<(T, T)>, height_1: nat, height_2: nat)
    requires height_2 <= |rel|
    requires height_1 <= height_2
    ensures trans_closure_helper(rel, height_2) >= trans_closure_helper(rel, height_1)
  {
  }

  lemma TransClosureMembership<T(!new)>(rel: set<(T, T)>, e1: T, e2: T) returns (m : nat)
    requires (e1, e2) in trans_closure(rel)
    ensures m <= |rel|
    ensures (e1, e2) in compose_n(rel, m)
    ensures not_in_lower(rel, m, e1, e2)
  {
    reveal trans_closure;
    assert not_in_lower(rel, 0, e1, e2) by {
      reveal not_in_lower;
    }
    var res := TransClosureHelperMembership(rel, |rel|, e1, e2);
    return res;
  }

  // not sure why this is slow now...
  lemma TransClosureHelperMembership<T(!new)>(rel: set<(T, T)>, depth: nat, e1: T, e2: T) returns (m : nat)
    requires depth <= |rel|
    requires (e1, e2) in trans_closure_helper(rel, depth)
    requires not_in_lower(rel, |rel| - depth, e1, e2)
    decreases depth
    ensures m <= |rel|
    ensures (e1, e2) in compose_n(rel, m)
    ensures not_in_lower(rel, m, e1, e2)
  {
    if depth == 0 {
      assert |rel| <= |rel|;
      return |rel|;
    } else { // inductive case
      if (e1, e2) in compose_n(rel, |rel| - depth) {
        assert |rel| - depth <= |rel|;
        return |rel| - depth;
      } else {
        NotInLowerAndNotInComposeNMeansNotInLower(rel, |rel| - depth, e1, e2);
        var res := TransClosureHelperMembership(rel, depth - 1, e1, e2);
        return res;
      }
    }
  }




  lemma InComposeNMinMeansUniqueNSequenceExists<T(!new)>(rel: set<(T,T)>, n: nat, e1: T, e2: T) returns (s: seq<(T, T)>)
    requires (e1, e2) in compose_n(rel, n)
    requires not_in_lower(rel, n, e1, e2)
    ensures chain(s, rel, n, e1, e2)
    ensures unique(s)
  {
    reveal compose_n;
    if n == 0 {
      assert false;
    } else {
      if n == 1 {
        var s := [ (e1, e2) ]; // trigger the existence of the sequence
        assert chain(s, rel, 1, e1, e2) by {
          SingletonChain(rel, e1, e2);
        }
        assert unique(s) by {
          reveal unique;
        }
        return s;
      } else { // inductive case
        assert (e1, e2) in compose(rel, compose_n(rel, n - 1));
        var emid :| (e1, emid) in rel && (emid, e2) in compose_n(rel, n - 1);
        NotInLowerSubChain(rel, n, e1, e2, emid);

        var s := InComposeNMinMeansUniqueNSequenceExists(rel, n - 1, emid, e2);
        // var s : seq<(T, T)> :| chain(s, rel, n - 1, emid, e2) && unique(s);
        var s' := [(e1, emid)] + s;
        assert chain(s', rel, n, e1, e2) by {
          SingletonChain(rel, e1, emid);
          CombinedChainIsChain([(e1, emid)], s, rel, 1, n - 1, e1, emid, e2);
        }
        AddingNewToUniqueIsUnique(rel, n, e1, e2, emid, s, s');
        return s';
      }
    }
  }

  lemma ChainNMeansInComposeN<T(!new)>(rel: set<(T,T)>, n: nat, e1: T, e2: T, s: seq<(T, T)>)
    requires n > 0
    requires chain(s, rel, n, e1, e2)
    ensures (e1, e2) in compose_n(rel, n)
  {
    reveal compose_n;
    if n == 1 {
      assert s == [ (e1, e2) ] by {
        reveal chain;
      }
      assert (e1, e2) in compose_n(rel, 1) by {
        reveal chain;
      }
    } else {
      assert |s| > 1 by { reveal chain; }
      var emid := s[1].0;
      assert (e1, emid) in rel by { reveal chain; }
      assert chain(s[1..], rel, n - 1, emid, e2) by {
        reveal chain;
      }
      ChainNMeansInComposeN(rel, n - 1, emid, e2, s[1..]);
    }
  }

}