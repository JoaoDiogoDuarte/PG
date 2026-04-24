(* Folding test file exercising every grammar construct supported
   by pg-ec-toggle-hiding.

   How to test:
     1. Open this file in easycrypt-mode.
     2. Put point anywhere inside one of the labelled regions below.
     3. Press C-c w — the region should collapse into an inline
        "[KIND NAME folded ...]" marker.
     4. Press C-c w again on the header line (or the marker) to unfold.
     5. Try typing inside a folded region — Emacs should refuse.

   The innermost region containing point wins, so e.g. folding inside
   a lemma inside a section inside a theory folds just the lemma
   first; unfolding it and folding again from the section header
   folds the section; and so on. *)

require import Int.

(* =============== *)
(* Comment folding *)
(* =============== *)

(** A doc-style comment.
    Put point inside and press C-c w — the whole comment collapses.
    Nested (* inner comments *) are part of this outer fold. *)

(* ========= *)
(* Theory    *)
(* ========= *)

theory Arith.

  axiom add_comm : forall (x y : int), x + y = y + x.

  axiom add_assoc :
    forall (x y z : int),
      (x + y) + z = x + (y + z).

  (* --- Ops (simple form) --- *)

  op zero : int = 0.

  op succ (n : int) : int = n + 1.

  const forty_two : int = 42.

  (* --- Op with `with' cases --- *)

  op is_zero (n : int) =
    with n = 0  => true
    with n = _  => false.

  (* --- Section inside a theory --- *)

  section Named.
    lemma zero_add : forall (x : int), 0 + x = x.
    proof.
      move=> x.
      by rewrite add_comm.
    qed.

    lemma add_zero_by : forall (x : int), x + 0 = x by smt().

    equiv trivial_equiv :
      true ==> true.
    proof. by []. qed.

    hoare trivial_hoare : true ==> true.
    proof. by []. qed.
  end section Named.

  (* --- Anonymous section --- *)

  section.
    lemma anon_lemma : 1 + 1 = 2.
    proof. by []. qed.
  end section.

end Arith.

(* ============== *)
(* Nested theory  *)
(* ============== *)

theory Outer.
  theory Inner.
    axiom inner_ax : true.
    op inner_op : int = 7.
  end Inner.

  lemma outer_lemma : true.
  proof. by []. qed.
end Outer.

(* ======= *)
(* Clones  *)
(* ======= *)

clone import Arith as A1.

clone include Arith with
  op zero <- 0,
  op succ <- fun n => n + 1.

clone Arith as A2 with
  op zero <- 0.

(* ====================== *)
(* Top-level proof blocks *)
(* ====================== *)

lemma toplevel_lemma : forall (x : int), x = x.
proof. by move=> x. qed.

lemma toplevel_by : 2 = 2 by [].

equiv toplevel_equiv : true ==> true.
proof. by []. qed.

phoare toplevel_phoare : [ true ==> true ] = 1%r.
proof. admitted.

(* ======================== *)
(* Admitted / abort endings *)
(* ======================== *)

lemma to_admit : 3 = 3.
proof.
  admit.
admitted.

lemma to_abort : 4 = 4.
proof.
  trivial.
abort.
