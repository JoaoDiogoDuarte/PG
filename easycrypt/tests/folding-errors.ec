(* Error-handling test file for pg-ec-toggle-hiding.

   Each scenario below is intentionally malformed.  To test one,
   comment out the OTHER scenarios (wrap them in (* ... *)) so that
   only one malformed construct is live, then put point inside it
   and press C-c w.  You should get a user-visible error such as:

     - "Mismatched `end section' ..."
     - "Unclosed `section ...' opened at line N"
     - "Section name mismatch: `X' opened ..., closed with `Y' ..."
     - "Named `end section Y' closes unnamed section ..."
     - "Unnamed `end section' closes named section `X' ..."
     - "Point is not inside any section"

   The buffer must be otherwise well-formed for the folder to
   succeed, hence the "comment-out the rest" instruction. *)

require import Int.

(* ====================================================== *)
(* Scenario E1: stray `end section' with no opening header.
   Put point on the `end section' line and press C-c w. *)

end section.

(* ====================================================== *)
(* Scenario E2: section opened but never closed.
   Put point inside the body below and press C-c w. *)

section Forever.
  lemma l_forever : 1 = 1.
  proof. by []. qed.

(* ====================================================== *)
(* Scenario E3: name mismatch between header and footer. *)

section Alpha.
  lemma l_mismatch : 2 = 2.
  proof. by []. qed.
end section Beta.

(* ====================================================== *)
(* Scenario E4: named header closed by anonymous footer. *)

section Gamma.
  lemma l_g : 3 = 3.
  proof. by []. qed.
end section.

(* ====================================================== *)
(* Scenario E5: anonymous header closed by named footer. *)

section.
  lemma l_anon_named : 4 = 4.
  proof. by []. qed.
end section Delta.

(* ====================================================== *)
(* Scenario E6: point is not inside any section.

   Put point on THIS line (between the E5 block above and the
   well-formed section below) and press C-c w while no other
   scenario is active.  Expected error:
   "Point is not inside any section".  *)

section Ok.
  lemma l_ok : 5 = 5.
  proof. by []. qed.
end section Ok.
