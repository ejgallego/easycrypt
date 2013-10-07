(* A theory of polymorphic arrays. *)

(*
 * All operators are only partially specified, as we may choose to match
 * them with various programming language constructs.
 * 
 * The user wanting to instantiate it with particular implementation
 * choices should clone it and add axioms to further refine the
 * operators.
 *
 * The operator names for imperative operators correspond to the OCaml Array library.
 *
 *)

require import Logic.
require import Int.
require Fun. (* For reasoning about higher-order operators *)

(*********************************)
(*             Core              *)
(*********************************)
(* A type *)
type 'x array.

(* Arrays have a non-negative length *)
op length: 'x array -> int.
axiom length_pos: forall (xs:'x array), 0 <= length xs.

(* And a bunch of elements *)
op "_.[_]": 'x array -> int -> 'x.

(* Equality is extensional *)
pred (==) (xs0 xs1:'x array) =
  length xs0 = length xs1 /\
  forall (i:int), 0 <= i < length xs0 => xs0.[i] = xs1.[i].

axiom array_ext (xs0 xs1:'x array):
  xs0 == xs1 => xs0 = xs1.

lemma rw_array_ext (xs0 xs1:'x array):
  xs0 == xs1 <=> xs0 = xs1.
proof strict.
by split; first apply array_ext.
qed.

(*********************************)
(*    "Functional" Operators     *)
(*********************************)
(* empty *)
op empty: 'x array.

axiom length_empty: length (empty<:'x>) = 0.

lemma empty_unique (xs:'x array):
  length(xs) = 0 => xs = empty.
proof strict.
by intros=> xs_0; apply array_ext; split;
     [rewrite length_empty | smt].
qed.

(* cons *)
op "_::_" : 'x -> 'x array -> 'x array.

axiom length_cons (x:'x) (xs:'x array):
  length (x::xs) = 1 + length xs.

axiom get_cons (x:'x) (xs:'x array) (i:int):
  0 <= i <= length xs =>
  (x::xs).[i] = (0 = i) ? x : xs.[i - 1].

lemma cons_nonempty (x:'x) (xs:'x array):
  x::xs <> empty.
proof strict.
by rewrite -not_def=> cons_empty;
   cut:= fcongr length (x::xs) empty _=> //;
   rewrite length_empty length_cons; smt.
qed.

lemma consI (x y:'x) (xs ys:'x array):
  x::xs = y::ys <=> x = y /\ xs = ys.
proof strict.
split; last by intros=> [-> ->].
rewrite - !rw_array_ext /(==)=> [len val].
do !split.
  cut:= val 0 _; first smt.
  by rewrite 2?get_cons /=; first 2 smt.
  by generalize len; rewrite 2!length_cons; smt.
  intros=> i i_bnd; cut := val (i + 1) _; first smt.
  rewrite 2?get_cons; first 2 smt.
  by cut ->: (0 = i + 1) = false by smt; cut ->: i + 1 - 1 = i by smt.
qed.

(* snoc *)
op (:::): 'x array -> 'x -> 'x array.

axiom length_snoc (x:'x) (xs:'x array):
  length (xs:::x) = length xs + 1.

axiom get_snoc (xs:'x array) (x:'x) (i:int):
  0 <= i <= length xs =>
  (xs:::x).[i] = (i < length xs) ? xs.[i] : x.

lemma snoc_nonempty (xs:'x array, x:'x):
  xs:::x <> empty.
proof strict.
by rewrite -not_def=> snoc_empty;
   cut:= fcongr length (xs:::x) empty _=> //;
   rewrite length_empty length_snoc; smt.
qed.

(* Induction Principle *)
axiom array_ind (p:'x array -> bool):
  p empty =>
  (forall x xs, p xs => p (x::xs)) =>
  (forall xs, p xs).

(***************************)
(*      OCaml Arrays       *)
(***************************)
(* set *)
op "_.[_<-_]": 'x array -> int -> 'x -> 'x array.

axiom length_set (i:int) (x:'x) (xs:'x array):
  length (xs.[i <- x]) = length xs.

axiom get_set (xs:'x array) (i j:int) (x:'x):
  0 <= j < length xs =>
  xs.[i <- x].[j] = (i = j) ? x : xs.[j].

lemma set_set i j (x y:'x) xs:
  xs.[i <- x].[j <- y] =
    (i = j) ? xs.[j <- y] :
              xs.[j <- y].[i <- x].
proof strict.
by apply array_ext; split; smt.
qed.

lemma nosmt set_setE x i (y:'a) xs:
  xs.[i <- x].[i <- y] = xs.[i <- y].
proof strict.
by rewrite set_set.
qed.

lemma nosmt set_setN x i j (y:'a) xs:
  i <> j =>
  xs.[i <- x].[j <- y] = xs.[j <- y].[i <- x].
proof strict.
by rewrite set_set -rw_neqF=> ->.
qed.

(* make *)
op make: int -> 'x -> 'x array.

axiom length_make (x:'x) l:
  0 <= l =>
  length (make l x) = l.

axiom get_make l (x:'x) i:
  0 <= i < l =>
  (make l x).[i] = x.

(* init *)
op init: int -> (int -> 'x) -> 'x array.

axiom length_init (f:int -> 'x) l:
  0 <= l =>
  length (init l f) = l.

axiom get_init l (f:int -> 'x) i:
  0 <= i < l =>
  (init l f).[i] = f i.

(* append *)
op (||): 'x array -> 'x array -> 'x array.

axiom length_append (xs0 xs1:'x array):
  length (xs0 || xs1) = length xs0 + length xs1.

axiom get_append (xs0 xs1:'x array) (i:int):
  0 <= i < length (xs0 || xs1) =>
  (xs0 || xs1).[i] = (0 <= i < length xs0) ? xs0.[i] : xs1.[i - length xs0].

(* sub *)
op sub: 'x array -> int -> int -> 'x array.

axiom length_sub (xs:'x array) (s l:int):
  0 <= s => 0 <= l => s + l <= length xs =>
  length (sub xs s l) = l.

axiom get_sub (xs:'x array) (s l i:int):
  0 <= s => 0 <= l => s + l <= length xs =>
  0 <= i < l =>
  (sub xs s l).[i] = xs.[i + s].

(* fill *)
op fill: 'x array -> int -> int -> 'x -> 'x array.

axiom length_fill (s l:int) x (xs:'x array):
  0 <= s => 0 <= l => s + l <= length xs =>
  length (fill xs s l x) = length xs.

axiom get_fill (xs:'x array) (s l:int) x i:
  0 <= s => 0 <= l => s + l <= length xs =>
  0 <= i < length xs =>
  (fill xs s l x).[i] = (s <= i < s + l) ? x : xs.[i].

(* blit (previously write) *)
op blit: 'x array -> int -> 'x array -> int -> int -> 'x array.

axiom length_blit (dst src:'x array) (dOff sOff l:int):
  0 <= dOff => 0 <= sOff => 0 <= l =>
  dOff + l <= length dst =>
  sOff + l <= length src =>
  length (blit dst dOff src sOff l) = length dst.

axiom get_blit (dst src:'x array) (dOff sOff l i:int):
  0 <= dOff => 0 <= sOff => 0 <= l =>
  dOff + l <= length dst =>
  sOff + l <= length src =>
  0 <= i < length dst =>
  (blit dst dOff src sOff l).[i] =
    (dOff <= i < dOff + l) ? src.[i - dOff + sOff]
                           : dst.[i].

(* map *)
op map: ('x -> 'y) -> 'x array -> 'y array.

axiom length_map (xs:'x array) (f:'x -> 'y):
  length (map f xs) = length xs.

axiom get_map (xs:'x array) (f:'x -> 'y, i:int):
  0 <= i < length(xs) =>
  (map f xs).[i] = f (xs.[i]).

(* map2 *) (* Useful for bitwise operations *)
op map2: ('x -> 'y -> 'z) -> 'x array -> 'y array -> 'z array.

axiom length_map2 (xs:'x array) (ys:'y array) (f:'x -> 'y -> 'z):
  length xs = length ys =>
  length (map2 f xs ys) = length xs.

axiom get_map2 (xs:'x array) (ys:'y array) (f:'x -> 'y -> 'z, i:int):
  length xs = length ys =>
  0 <= i < length xs =>
  (map2 f xs ys).[i] = f (xs.[i]) (ys.[i]).

(* mapi *)
op mapi: (int -> 'x -> 'y) -> 'x array -> 'y array.

axiom length_mapi (f:int -> 'x -> 'y) (xs:'x array):
  length (mapi f xs) = length xs.

axiom get_mapi (f:int -> 'x -> 'y) (xs:'x array) (i:int):
  0 <= i < length xs =>
  (mapi f xs).[i] = f i (xs.[i]).

(* fold_left *)
op fold_left: ('state -> 'x -> 'state) -> 'state -> 'x array -> 'state.

axiom fold_left_empty (f:'state -> 'x -> 'state) s:
  (fold_left f s empty) = s.

axiom fold_left_cons (f:'state -> 'x -> 'state) s xs:
  0 < length xs =>
  (fold_left f s xs) = f (fold_left f s (sub xs 1 (length xs - 1))) xs.[0].

(* fold_right *)
op fold_right: ('state -> 'x -> 'state) -> 'state -> 'x array -> 'state.

axiom fold_right_empty (f:'state -> 'x -> 'state) s:
  (fold_right f s empty) = s.

axiom fold_right_cons (f:'state -> 'x -> 'state) s xs:
  0 < length xs =>
  (fold_right f s xs) = fold_right f (f s xs.[0]) (sub xs 1 (length xs - 1)).

(* lemmas *)
lemma empty_append_l (xs:'x array):
  (xs || empty) = xs.
proof strict.
apply array_ext; split.
  by rewrite length_append length_empty.
  by intros=> i; rewrite length_append length_empty /= => i_bnd;
     rewrite get_append ?length_append ?length_empty /= // i_bnd.
qed.

lemma empty_append_r (xs:'x array):
  (empty || xs) = xs.
proof strict.
apply array_ext; split.
  by rewrite length_append length_empty.
  by intros=> i; rewrite length_append length_empty /= => i_bnd;
     rewrite get_append ?length_append ?length_empty /= //;
     cut ->: (0 <= i < 0) = false by smt.
qed.

lemma sub_full (xs:'x array):
  sub xs 0 (length xs) = xs.
proof strict.
apply array_ext; split.
  by rewrite length_sub; first 2 smt.
  by intros=> i; rewrite length_sub //=; first 2 smt.
qed.

lemma sub_append_l (xs0 xs1:'x array):
  sub (xs0 || xs1) 0 (length xs0) = xs0.
proof strict.
by apply array_ext; split; smt.
qed.

lemma sub_append_r (xs0 xs1:'x array):
  sub (xs0 || xs1) (length xs0) (length xs1) = xs1.
proof strict.
by apply array_ext; split; smt.
qed.

lemma sub_append_sub (xs:'x array) (i l1 l2:int):
  0 <= i => 0 <= l1 => 0 <= l2 => i + l1 + l2 <= length xs =>
  (sub xs i l1 || sub xs (i + l1) l2) = sub xs i (l1 + l2).
proof strict.
by intros=> i_pos l1_pos l2_pos i_l1_l2_bnd;
   apply array_ext; split; smt.
qed.

(* Useless? *)
lemma fold_left_deterministic: forall (f1 f2:'state -> 'x -> 'state) s1 s2 xs1 xs2,
  f1 = f2 => s1 = s2 => xs1 = xs2 =>
  fold_left f1 s1 xs1 = fold_left f2 s2 xs2
by [].

(* This proof needs cleaned up, and the lemma library completed. *)
lemma fold_length (xs:'x array):
  fold_left (lambda n x, n + 1) 0 xs = length xs.
proof strict.
elim/array_ind xs.
  by rewrite fold_left_empty length_empty.
  by intros=> {xs} x xs IH; rewrite fold_left_cons;
       [ | cut ->: sub (x::xs) 1 (length (x::xs) - 1) = xs by (apply array_ext; smt)];
     smt.
qed.

lemma blit_append (dst src:'x array):
  length src <= length dst =>
  blit dst 0 src 0 (length src) = (src || (sub dst (length src) (length dst - length src))).
proof strict.
intros=> src_dst; apply array_ext; split; smt.
qed.

(** Logical Stuff *)
(* all: this is computable because all arrays are finite *)
op all: ('x -> bool) -> 'x array -> bool.

axiom all_def p (xs:'x array):
  all p xs <=>
  (forall i, 0 <= i < length xs => p xs.[i]).

(* alli *)
op alli: (int -> 'x -> bool) -> 'x array -> bool.

axiom alli_def p (xs:'x array):
  alli p xs <=>
  (forall i, 0 <= i < length xs => p i xs.[i]).

(** Distribution on 'a array of length k from distribution on 'a *)
theory Darray.
  require import Distr.
  require import Real.

  op darray: int -> 'a distr -> 'a array distr.

  axiom mu_x0 (len:int) (d:'a distr) (x:'a array):
    len < 0 => mu_x (darray len d) x = 0%r.

  axiom mu_x_def (len: int) (d:'a distr) (x:'a array):
    0 <= len =>
    mu_x (darray len d) x = fold_right (lambda p x, p * mu_x d x) 1%r x.

  axiom supp_def (len:int) (x:'a array) (d:'a distr):
    in_supp x (darray len d) <=>
    (0 <= len /\ length x = len /\ all (support d) x).

  lemma supp_full (len:int) (d:'a distr) (x:'a array):
    (forall y, in_supp y d) =>
    length x = len =>
    in_supp x (darray len d).
  proof strict.
  intros dF Hlen; rewrite Darray.supp_def; do !split=> //; first smt.
  by rewrite all_def=> i Hi; rewrite /support dF.
  qed.

  lemma supp_len (len:int) (x: 'a array) (d:'a distr):
    in_supp x (darray len d) =>
    length x = len.
  proof strict. by rewrite supp_def. qed.

  lemma supp_k (len:int) (x: 'a array) (d:'a distr) (k:int):
    0 <= k < len =>
    in_supp x (darray len d) =>
    in_supp x.[k] d.
  proof strict.
  rewrite supp_def -/(support d x.[k])=> Hk [H1 [H2 H3]]; subst len.
  by generalize H3; rewrite all_def=> H3; apply H3.
  qed.

  (* This would be a lemma by definition of ^
     if we had it in the correct form *)
  axiom weight_d (d:'a distr) len:
    0 <= len =>
    weight (darray len d) = (weight d) ^ len.

  lemma darrayL (d:'a distr) len:
    0 <= len =>
    weight d = 1%r =>
    weight (darray len d) = 1%r.
  proof strict.
  intros leq0_len H; rewrite (weight_d d len) // H.
  smt "Alt-Ergo".
  qed.

  axiom uniform (d:'a distr) len:
    0 <= len =>
    isuniform d =>
    isuniform (darray len d).
end Darray.
