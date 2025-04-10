open Printf
module NeighborSet = Set.Make (String)

type neighborst = NeighborSet.t

module Graph = Map.Make (String)

type grapht = neighborst Graph.t

module StringSet = Set.Make (String)

type livet = StringSet.t

let empty : grapht = Graph.empty

let add_node (g : grapht) (name : string) : grapht =
  if Graph.mem name g then
    g
  else
    Graph.add name NeighborSet.empty g
;;

let add_directed_edge (g : grapht) (n1 : string) (n2 : string) : grapht =
  let g' = add_node (add_node g n1) n2 in
  let curr_neighbors = Graph.find n1 g' in
  Graph.add n1 (NeighborSet.add n2 curr_neighbors) g'
;;

let add_edge (g : grapht) (n1 : string) (n2 : string) : grapht =
  let g' = add_directed_edge g n1 n2 in
  add_directed_edge g' n2 n1
;;

let get_neighbors (g : grapht) (name : string) : string list =
  if Graph.mem name g then
    NeighborSet.fold (fun n ns -> n :: ns) (Graph.find name g) []
  else
    []
;;

let get_vertices (g : grapht) : string list =
  let keys, _ = List.split (Graph.bindings g) in
  keys
;;

let string_of_graph (g : grapht) : string =
  let string_of_neighbors (n : string) : string = ExtString.String.join ", " (get_neighbors g n) in
  ExtString.String.join "\n"
    (List.map (fun k -> sprintf "%s: %s" k (string_of_neighbors k)) (get_vertices g))
;;

(* ========================== *)
(* =  Additional functions  = *)
(* ========================== *)

let add_nodes g nodes =
  List.fold_left (fun g' n -> add_node g' n) g nodes

let remove_node (g : grapht) (name : string) : grapht =
  let g' = Graph.remove name g in
  Graph.map (fun neighbors -> NeighborSet.remove name neighbors) g'
;;

let degree (g : grapht) (name : string) : int = NeighborSet.cardinal (Graph.find name g)

let smallest_degree (g : grapht) : string option =
  let random_node = Graph.choose_opt g in
  match random_node with
  | None -> None
  | Some (node, _) ->
      Some
        (Graph.fold
           (fun name neighbors smallest ->
             if NeighborSet.cardinal neighbors < degree g smallest then
               name
             else
               smallest )
           g node )
;;

(* Merges two graphs, taking the union of their edges. *)
let merge_graphs (g1 : grapht) (g2 : grapht) : grapht = 
  Graph.union (fun _ (set1 : neighborst) (set2 : neighborst) -> Some (NeighborSet.union set1 set2)) g1 g2

let connect (node : string) (nodes : neighborst) (g : grapht) : grapht =
  StringSet.fold (fun n g' -> add_edge g' node n) nodes g

let connect2 nodes1 nodes2 g : grapht =
  StringSet.fold (fun n g' -> connect n nodes2 g') nodes1 g

let connect_set nodes g : grapht = 
  connect2 nodes nodes g