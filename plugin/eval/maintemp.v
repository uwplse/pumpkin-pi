Require Import Ornamental.Ornaments.
Require Import PeanoNat Nat List Sorting.Permutation.
Require Import lemmas cast main.
Import ListNotations.

Open Scope bool_scope.

(*
 * Temporary tests to make sure IP lifting isn't broken
 *)

Lift induction NatCaseStudy.Sized.orn_size NatCaseStudy.Sized.orn_size_inv in NatCaseStudy.Base.preorder as preorder'_ind.
Print preorder'_ind.

Lift induction NatCaseStudy.Sized.orn_size NatCaseStudy.Sized.orn_size_inv in NatCaseStudy.Base.inorder as inorder'_ind.
Print inorder'_ind.

Lift induction NatCaseStudy.Sized.orn_size NatCaseStudy.Sized.orn_size_inv in NatCaseStudy.Base.postorder as postorder'_ind.
Print postorder'_ind.

Lift induction NatCaseStudy.Sized.orn_size NatCaseStudy.Sized.orn_size_inv in NatCaseStudy.Base.mirror as mirror'_ind.
Print mirror'_ind.

Lift induction NatCaseStudy.Sized.orn_size NatCaseStudy.Sized.orn_size_inv in NatCaseStudy.Base.pre_permutes as pre_permutes'_ind.
Print pre_permutes'_ind.

Lift induction NatCaseStudy.Sized.orn_size NatCaseStudy.Sized.orn_size_inv in NatCaseStudy.Base.post_permutes as post_permutes'_ind.
Print post_permutes'_ind.

Lift induction NatCaseStudy.Sized.orn_size NatCaseStudy.Sized.orn_size_inv in NatCaseStudy.Base.mirror_permutes as mirror_permutes'_ind.
Print mirror_permutes'_ind.

Lift induction NatCaseStudy.Measured.orn_height NatCaseStudy.Measured.orn_height_inv in NatCaseStudy.Base.preorder as preorder'_ind2.
Print preorder'_ind2.

Lift induction NatCaseStudy.Measured.orn_height NatCaseStudy.Measured.orn_height_inv in NatCaseStudy.Base.inorder as inorder'_ind2.
Print inorder'_ind2.

Lift induction NatCaseStudy.Measured.orn_height NatCaseStudy.Measured.orn_height_inv in NatCaseStudy.Base.postorder as postorder'_ind2.
Print postorder'_ind2.

Lift induction NatCaseStudy.Measured.orn_height NatCaseStudy.Measured.orn_height_inv in NatCaseStudy.Base.mirror as mirror'_ind2.
Print mirror'_ind2.

Lift  induction NatCaseStudy.Measured.orn_height NatCaseStudy.Measured.orn_height_inv in NatCaseStudy.Base.pre_permutes as pre_permutes'_ind2.
Print pre_permutes'_ind2.

Lift induction NatCaseStudy.Measured.orn_height NatCaseStudy.Measured.orn_height_inv in NatCaseStudy.Base.post_permutes as post_permutes'_ind2.
Print post_permutes'_ind2.

Lift induction NatCaseStudy.Measured.orn_height NatCaseStudy.Measured.orn_height_inv in NatCaseStudy.Base.mirror_permutes as mirror_permutes'_ind2.
Print mirror_permutes'_ind2.

Lift induction NatCaseStudy.Heaped._orn_heap NatCaseStudy.Heaped._orn_heap_inv in NatCaseStudy.Measured.preorder as _preorder'_ind3.
Print _preorder'_ind3.  

Lift induction NatCaseStudy.Heaped.orn_heap NatCaseStudy.Heaped.orn_heap_inv in NatCaseStudy.Heaped._preorder as preorder'_ind3.
Print preorder'_ind3.

Lift induction NatCaseStudy.Heaped._orn_heap NatCaseStudy.Heaped._orn_heap_inv in NatCaseStudy.Measured.inorder as _inorder'_ind3.
Print _inorder'_ind3.

Lift induction NatCaseStudy.Heaped.orn_heap NatCaseStudy.Heaped.orn_heap_inv in NatCaseStudy.Heaped._inorder as inorder'_ind3.
Print inorder'_ind3.

Lift induction NatCaseStudy.Heaped._orn_heap NatCaseStudy.Heaped._orn_heap_inv in NatCaseStudy.Measured.postorder as _postorder'_ind3.
Print _postorder'_ind3.

Lift induction NatCaseStudy.Heaped.orn_heap NatCaseStudy.Heaped.orn_heap_inv in NatCaseStudy.Heaped._postorder as postorder'_ind3.
Print postorder'_ind3.

Lift induction NatCaseStudy.Ordered.__orn_order NatCaseStudy.Ordered.__orn_order_inv in NatCaseStudy.Base.preorder as __preorder'_ind4.
Print __preorder'_ind4.

Lift induction NatCaseStudy.Ordered._orn_order NatCaseStudy.Ordered._orn_order_inv in NatCaseStudy.Ordered.__preorder as _preorder'_ind4.
Print _preorder'_ind4.

Lift induction NatCaseStudy.Ordered.orn_order NatCaseStudy.Ordered.orn_order_inv in NatCaseStudy.Ordered._preorder as preorder'_ind4.
Print preorder'_ind4.

Lift induction NatCaseStudy.Ordered.__orn_order NatCaseStudy.Ordered.__orn_order_inv in NatCaseStudy.Base.inorder as __inorder'_ind4.
Print __inorder'_ind4.

Lift induction NatCaseStudy.Ordered._orn_order NatCaseStudy.Ordered._orn_order_inv in NatCaseStudy.Ordered.__inorder as _inorder'_ind4.
Print _inorder'_ind4.

Lift induction NatCaseStudy.Ordered.orn_order NatCaseStudy.Ordered.orn_order_inv in NatCaseStudy.Ordered._inorder as inorder'_ind4.
Print inorder'_ind4.

Lift induction NatCaseStudy.Ordered.__orn_order NatCaseStudy.Ordered.__orn_order_inv in NatCaseStudy.Base.postorder as __postorder'_ind4.
Print __postorder'_ind4.

Lift induction NatCaseStudy.Ordered._orn_order NatCaseStudy.Ordered._orn_order_inv in NatCaseStudy.Ordered.__postorder as _postorder'_ind4.
Print _postorder'_ind4.

Lift induction NatCaseStudy.Ordered.orn_order NatCaseStudy.Ordered.orn_order_inv in NatCaseStudy.Ordered._postorder as postorder'_ind4.
Print postorder'_ind4.

Lift induction NatCaseStudy.Balanced._orn_balance NatCaseStudy.Balanced._orn_balance_inv in NatCaseStudy.Ordered.preorder as _preorder'_ind5.
Print _preorder'_ind5.

Lift induction NatCaseStudy.Balanced.orn_balance NatCaseStudy.Balanced.orn_balance_inv in NatCaseStudy.Balanced._preorder as preorder'_ind5.
Print preorder'_ind5.

Lift induction NatCaseStudy.Balanced._orn_balance NatCaseStudy.Balanced._orn_balance_inv in NatCaseStudy.Ordered.inorder as _inorder'_ind5.
Print _inorder'_ind5.

Lift induction NatCaseStudy.Balanced.orn_balance NatCaseStudy.Balanced.orn_balance_inv in NatCaseStudy.Balanced._inorder as inorder'_ind5.
Print inorder'_ind5.

Lift induction NatCaseStudy.Balanced._orn_balance NatCaseStudy.Balanced._orn_balance_inv in NatCaseStudy.Ordered.postorder as _postorder'_ind5.
Print _postorder'_ind5.

Lift induction NatCaseStudy.Balanced.orn_balance NatCaseStudy.Balanced.orn_balance_inv in NatCaseStudy.Balanced._postorder as postorder'_ind5.
Print postorder'_ind5.

Lift induction NatCaseStudy.Balanced._orn_balance NatCaseStudy.Balanced._orn_balance_inv in @NatCaseStudy.Ordered.search as _search'_ind5.
Print _search'_ind5.

Lift induction NatCaseStudy.Balanced.orn_balance NatCaseStudy.Balanced.orn_balance_inv in @NatCaseStudy.Balanced._search as search'_ind5.
Print search'_ind5.
