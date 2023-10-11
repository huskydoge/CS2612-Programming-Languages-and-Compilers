```
(** SetsClass库中提供了一系列有关集合运算的性质的证明。未来大家在证明中既可以使
    用_[sets_unfold]_与_[rels_unfold]_将关于集合运算的命题转化为关于逻辑的命题，
    也可以直接使用下面这些性质完成证明。  

      Sets_equiv_Sets_included:
    forall x y, x == y <-> x ⊆ y /\ y ⊆ x;
  Sets_empty_included:
    forall x, ∅ ⊆ x;
  Sets_included_full:
    forall x, x ⊆ Sets.full;
  Sets_intersect_included1:
    forall x y, x ∩ y ⊆ x;
  Sets_intersect_included2:
    forall x y, x ∩ y ⊆ y;
  Sets_included_intersect:
    forall x y z, x ⊆ y -> x ⊆ z -> x ⊆ y ∩ z;
  Sets_included_union1:
    forall x y, x ⊆ x ∪ y;
  Sets_included_union2:
    forall x y, y ⊆ x ∪ y;
  Sets_union_included_strong2:
    forall x y z u,
       x ∩ u ⊆ z -> y ∩ u ⊆ z -> (x ∪ y) ∩ u ⊆ z;
  
      Sets_included_omega_union:
    forall xs n, xs n ⊆ ⋃ xs;  挑一个n第n个是子集
  Sets_omega_union_included:
    forall xs y, (forall n, xs n ⊆ y) -> ⋃ xs ⊆ y;
  Sets_omega_intersect_included:
    forall xs n, ⋂ xs ⊆ xs n;
  Sets_included_omega_intersect:
    forall xs y, (forall n : nat, y ⊆ xs n) -> y ⊆ ⋂ xs;
  
      Rels_concat_union_distr_r:
    forall x1 x2 y,
      (x1 ∪ x2) ∘ y == (x1 ∘ y) ∪ (x2 ∘ y);  如果变成一列的并，也会有这个性质。
  Rels_concat_union_distr_l:
    forall x y1 y2,
      x ∘ (y1 ∪ y2) == (x ∘ y1) ∪ (x ∘ y2);
  Rels_concat_mono:
    forall x1 x2,
      x1 ⊆ x2 ->
      forall y1 y2,
        y1 ⊆ y2 ->
        x1 ∘ y1 ⊆ x2 ∘ y2;
  Rels_concat_assoc:
    forall x y z,
      (x ∘ y) ∘ z == x ∘ (y ∘ z);
*)

```

