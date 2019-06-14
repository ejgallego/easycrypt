require import Ring List FSet Int.
require (*--*) FinType.

pragma -oldip. pragma +implicits.

(**************************************************************************)
clone include Ring.ZModule.

op enum: t list.
axiom enumS x: count (pred1 x) enum = 1.

clone include FinType with
  type  t         <- t,
  op    enum      <- enum
proof enum_spec by exact/enumS.

(**************************************************************************)
op is_subgroup (s : t fset) =
  zeror \in s /\
  forall x y, x \in s => y \in s => (x - y) \in s.

lemma subgroup_opp (s : t fset) x:
  is_subgroup s => x \in s => -x \in s.
proof.
rewrite /is_subgroup=> -[+ mems_sub] - /mems_sub h /h {h}.
by rewrite sub0r.
qed.

lemma subgroup_add (s : t fset) x y:
  is_subgroup s => x \in s => y \in s => x + y \in s.
proof.
move=> ^ /(subgroup_opp _ y) opp_y.
rewrite /is_subgroup=> -[_ mems_sub] /mems_sub + /opp_y - h /h.
by rewrite opprK.
qed.

(**************************************************************************)
op coset1 g H = oflist (map (fun x=> g + x) (elems H))
axiomatized by coset1E.

lemma coset1P g H x:
  (x \in coset1 g H <=> x - g \in H).
proof.
rewrite coset1E mem_oflist mapP; split=> [[h] [] /= + ->>|xg_in_H].
+ by rewrite -memE addrAC subrr add0r.
by exists (x - g)=> /=; rewrite -memE xg_in_H /= addrCA subrr addr0.
qed.

lemma coset1_bij a b H:
  exists f,
    bijective f /\
    coset1 b H = image f (coset1 a H).
proof.
exists (fun h=> b - a + h); split.
+ exists (fun h=> a - b + h); rewrite /cancel /=; split=> x.
  + by rewrite addrA addrCA addrA addrCA subrr addr0 subrr add0r.
  by rewrite addrA addrCA addrA addrCA subrr addr0 subrr add0r.
apply/fsetP=> h; rewrite imageP coset1P; split=> [hb_in_H|].
+ exists (a + h - b); rewrite coset1P /=.
  rewrite -!addrA (@addrA (-a)) (@addrC (-a)) subrr add0r.
  rewrite (@addrC h (-b)) (@addrA b (-b) h) subrr add0r //=.
  by rewrite addrC -!addrA (@addrC (-a) a) subrr addr0.
move=> [ah] [] /= + <<-; rewrite coset1P (@addrC b) -addrA (@addrC _ (-b)).
by rewrite -addrA (@addrA b (-b)) subrr add0r addrC.
qed.

lemma card_coset1_eq a b H:
  card (coset1 a H) = card (coset1 b H).
proof.
by move: (coset1_bij a b H)=> [f] [] [g] [] + _ -> - /fcard_image_eq ->.
qed.

lemma coset10 H: coset1 zeror H = H.
proof. by apply/fsetP=> x; rewrite coset1P subr0. qed.

lemma card_coset1 a H:
  card (coset1 a H) = card H.
proof. by rewrite -{2}coset10; exact/card_coset1_eq. qed.

lemma coset1_cover H:
  H <> fset0 =>
  forall x, exists a, x \in coset1 a H.
proof.
move=> /mem_pick pick_in_H x; exists (x - pick H).
by rewrite coset1P opprD addrA subrr add0r opprK.
qed.

lemma coset1_disjoint x a b H:
  is_subgroup H =>
  x \in coset1 a H =>
  x \in coset1 b H =>
  coset1 a H = coset1 b H.
proof.
move=> ^sg_H [] z_in_H H_subr_closed; rewrite !coset1P=> ha hb.
move: (H_subr_closed _ _ ha hb); rewrite addrAC opprD opprK addrA subrr add0r.
move=> hab; apply/fsetP=> z; rewrite !coset1P; split=> [hza|hzb].
+ move: (H_subr_closed _ _ hza hab).
  by rewrite addrAC opprD opprK -!addrA subrr addr0.
move: (subgroup_opp _ _ sg_H hzb)=> hbz; move: (H_subr_closed _ _ hbz hab).
rewrite opprD opprK opprD opprK addrA -(@addrA (-z)) subrr addr0.
by move=>/(subgroup_opp _ _ sg_H); rewrite opprD opprK.
qed.

(**************************************************************************)
op cosets H = oflist (map (fun g=> coset1 g H) enum)
axiomatized by cosetsE.

(**************************************************************************)
op gen x = oflist (filter (fun y=> exists n, y = intmul x n) enum)
axiomatized by genE.

lemma mem_gen y x:
  y \in gen x <=> exists n, y = intmul x n.
proof. by rewrite genE mem_oflist mem_filter enumP /=. qed.

lemma mem0_gen x: zeror \in gen x.
proof. by rewrite -(@mulr0z x) mem_gen; exists 0. qed.

lemma mem1_gen x: x \in gen x.
proof. by rewrite -{2}(@mulr1z x) mem_gen; exists 1. qed.

lemma is_subgroup_gen x: is_subgroup (gen x).
proof.
split=> [|y z]; first by exact/mem0_gen.
rewrite !mem_gen=> - [log_y ->>] [log_z ->>].
by exists (log_y - log_z); rewrite -mulrNz mulrzz_add.
qed.

(**************************************************************************)
op order x = card (gen x).
