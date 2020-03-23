module MyStack =

    type ImmutableStack<'T> =
        | Empty
        | NotEmpty  of 'T * ImmutableStack<'T>

    module ImmutableStack =
        let empty<'T> : ImmutableStack<'T> = Empty 

        let cons head tail = NotEmpty (head, tail)

        let pop stack = 
            match stack with
            | Empty -> None
            | NotEmpty (head, tail) -> Some (head, tail)

        let fold folder state stack =
            let rec recurse acc stack =
                match stack with
                | Empty -> acc
                | NotEmpty (h, t) -> recurse (folder acc h) t
            recurse state stack

        let length stack =
            let folder s v = s + 1
            fold folder 0 stack

        let rev stack =
            let folder s v =
                s |> cons v
            fold folder empty stack

        let map mapper stack =
            let folder state value = 
                state |> cons (mapper value)
            fold folder empty stack |> rev

        let toList stack =
            let folder s v =
                v::s
            fold folder [] stack |> List.rev

        let fromList l =
            let folder s v =
                s |> cons v
            List.fold folder empty l |> rev

    module Tests =
        open ImmutableStack
        open FsCheck

        type Properties = 
            class
                static member ``MyStack should behave like a stack``  (v: string) (vs : ImmutableStack<string>) =
                    // printfn "%A %A" v vs
            
                    let nvs = vs |> cons v
                    let e = Some (v, vs)
                    let a = nvs |> pop
                    e = a

                static member ``MyStack length after cons should increase by one``  (v: string) (vs : ImmutableStack<string>) =
                    // printfn "%A %A" v vs
                    let before = length vs
                    let nvs = vs |> cons v
                    let after = length nvs
                    (before + 1) = after

                static member ``MyStack length after pop should decrease by one`` (vs : ImmutableStack<string>) =
                    let before = length vs
                    let after = vs |> pop |> Option.map snd |> Option.map length |> Option.defaultValue -1
                    before = (after + 1)

                static member ``MyStack fromList then toList gives original result`` (vs : ImmutableStack<string>) =
                    let e = vs
                    let a = vs |> toList |> fromList
                    e = a

                // Using List.map as an oracle
                static member ``MyStack map should behave as per List map`` (vs : List<int>) =
                    let e = vs |> List.map (fun v -> v + 1)
                    let a = vs |> fromList |> map (fun v -> v + 1) |> toList
                    e = a

                static member ``Reversing MyStack twice should give back then original stack`` (vs : ImmutableStack<string>) =
                    let e = vs
                    let a = vs |> rev |> rev
                    e = a

            end
        
        let run () =
            let config = { Config.Quick  with MaxTest = 1000 }
            Check.All<Properties> config


module MyTree =
    type Colour = Red|Black
    type RedBlackTree<'K, 'V> =
        | Empty     // Is implicitly Black
        | Node      of Colour*'K*'V*RedBlackTree<'K, 'V>*RedBlackTree<'K, 'V>
    // §1 - Root node is always black
    // §2 - No red node has a red child
    // §3 - All branches root to leaf has the same number of black nodes
    // §2 + §3 -> Tree depth is at most 2*(log2 (n + 1))

    module RedBlackTree =
        let empty<'K, 'V> : RedBlackTree<'K, 'V> = Empty

        let rec depth tree =
            match tree with
            | Empty -> 0
            | Node (_, _, _, leftTree, rightTree) ->
                let leftDepth = depth leftTree
                let rightDepth = depth rightTree
                (max leftDepth rightDepth) + 1

        let rec lookup key tree =
            match tree with
            | Empty -> None
            | Node (_, k, v, l, r) -> 
                if key < k then
                    lookup key l
                elif key > k then
                    lookup key r
                elif key = k then
                    Some v
                else
                    failwith "Something bad happened"

        let rebalance t =
            match t with
            | Node (Black, zk, zv, Node (Red, yk, yv, Node (Red, xk, xv, a, b), c), d)
            | Node (Black, zk, zv, Node (Red, xk, xv, a, Node (Red, yk, yv, b, c)), d)
            | Node (Black, xk, xv, a, Node (Red, zk, zv, Node (Red, yk, yv, b, c), d))
            | Node (Black, xk, xv, a, Node (Red, yk, yv, b, Node (Red, zk, zv, c, d))) ->
                Node (Red, yk, yv, Node (Black, xk, xv, a, b), Node (Black, zk, zv, c, d))
            | _ -> t

        let rec setImpl key value tree =
            match tree with
            | Empty -> Node(Red, key, value, empty, empty)
            | Node (c, k, v, l, r) -> 
                if key < k then
                    let newLeft = setImpl key value l
                    Node(c, k, v, newLeft, r) |> rebalance
                elif key > k then
                    let newRight = setImpl key value r
                    Node(c, k, v, l, newRight) |> rebalance
                elif key = k then
                    Node(c, k, value, l, r)
                else
                    failwith "Something bad happened"

        let set key value tree =
            match setImpl key value tree with
            | Empty -> Empty
            | Node (_, k, v, l, r) -> Node (Black, k, v, l, r)

        let ofList l =
            let folder s (k, v) = set k v s
            l |> List.fold folder empty

    module TreeTests =
        open RedBlackTree
        open FsCheck

        let log2 n = log n/log 2.0

        type Key = int

        type Properties = 
            class
                static member ``RedBlackTree should contain value we set into it`` (key : Key) (value : int)  (keyValues : List<Key*int>) =               
                    let tree = keyValues |> ofList
                    let updatedTree = tree |> set key value
   
                    let e = Some (value)
                    let a = updatedTree |> lookup key

                    e = a

                static member ``RedBlackTree should contain all distinct keys`` (keyValues : List<Key*int>) =        
                    let kvs = keyValues |> List.distinctBy fst
                    let tree = kvs |> ofList

                    let e = kvs |> List.map (fun _      -> true)
                    let a = kvs |> List.map (fun (k, v) -> Some v = (tree |> lookup k))

                    e = a


                static member ``Arbitrary RedBackTree is roughly balanced`` (keyValues : List<Key*int>) =
                    let tree = keyValues |> ofList
                    let a = tree |> depth |> float
                    a <= 2.0 * log2 (1.0 + float (keyValues |> List.length))

                static member ``Arbitrary RedBackTree adheres to the Red-Black rule`` (keyValues : List<Key*int>) =
                   let t = keyValues |> ofList

                   let rec check t =
                     match t with
                     | Empty -> true
                     | Node (Red, _, _, Node(Red, _, _, _, _), _)
                     | Node (Red, _, _, _, Node(Red, _, _, _, _)) -> false
                     | Node (_, _, _, l, r) -> check l && check r

                   check t
                    
            end

        let run () =
            let config = { Config.Quick  with MaxTest = 1000 }
            Check.All<Properties> config


open System
open FsCheck

open MyStack
open ImmutableStack
open MyTree

[<EntryPoint>]
let main argv =

    
    TreeTests.run ()
    0
    