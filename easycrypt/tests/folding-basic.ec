(* Basic folding test file for pg-ec-toggle-hiding.

   How to test:
     1. Open this file in Emacs with Proof General loaded
        (M-x easycrypt-mode if not auto-selected).
     2. Put point on any line inside a section (or on its
        `section' / `end section' line) and press C-c w.
     3. The section body should collapse into an inline
        "[section ... folded ...]" marker.
     4. Press C-c w again on the marker / header to unfold.
     5. Try typing inside a folded region: Emacs should
        refuse with "Cannot edit folded EasyCrypt section". *)

require import Int.

(* ---- Case 1: single anonymous section ---- *)
section.
  lemma l_anon_1 : forall (x : int), x = x.
  proof. by move=> x. qed.

  lemma l_anon_2 : 1 + 1 = 2.
  proof. by []. qed.
end section.

(* ---- Case 2: single named section ---- *)
section Named.
  lemma l_named_1 : forall (x : int), x + 0 = x.
  proof. by move=> x. qed.
end section Named.

(* ---- Case 3: nested sections ----
   Put point inside INNER and press C-c w: only INNER folds.
   Put point in OUTER but outside INNER and fold: the whole
   OUTER (including INNER) folds. *)
section Outer.
  lemma l_outer_before : 0 = 0.
  proof. by []. qed.

  section Inner.
    lemma l_inner : forall (y : int), y - y = 0.
    proof. by move=> y. qed.
  end section Inner.

  lemma l_outer_after : 2 * 1 = 2.
  proof. by []. qed.
end section Outer.

(* ---- Case 4: deeply nested (3 levels) ---- *)
section A.
  section B.
    section C.
      lemma l_deep : true.
      proof. by []. qed.
    end section C.
  end section B.
end section A.

(* ---- Case 5: `section' tokens inside comments must be ignored.
   This must NOT confuse the folder:
     section Fake.
     end section Fake.
   Above two lines are inside a comment. *)

section Real.
  lemma l_real : 3 = 3.
  proof. by []. qed.
end section Real.
