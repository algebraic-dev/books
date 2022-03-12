type key = string
type 'a tree = Leaf | Node of 'a tree * key * 'a * 'a tree

let empty = Leaf

let rec insert key value = function
  | Leaf -> Node (empty, key, value, empty)
  | Node (l, k, v, r) when k > key -> Node (l, k, v, insert key value r)
  | Node (l, k, v, r) when k < key -> Node (insert key value l, k, v, r)
  | Node (_, _, _, _) as other -> other

let rec is_member key = function
  | Leaf -> false
  | Node (_, k, _, r) when k > key -> is_member key r
  | Node (l, k, _, _) when k < key -> is_member key l
  | Node (_, _, _, _) -> true

let rec lookup key = function
  | Leaf -> failwith "Not Found"
  | Node (_, k, _, r) when k > key -> lookup key r
  | Node (l, k, _, _) when k < key -> lookup key l
  | Node (_, _, v, _) -> v
