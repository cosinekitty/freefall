module Freefall.Partitions
open System.Collections.Generic

let rec Partitions (items: list<'T>) : IEnumerable<list<list<'T>>> =
    seq { 
        match items with
        | [] -> yield [ [] ]
        | [single] -> yield [ [single] ]
        | first :: rest -> 
            for subpart in Partitions rest do
                // For each sub-partition, we can place the first item by itself in a separate list.
                yield [first] :: subpart

                // The other N-1 possibilities are to put the first item in each of the remaining lists.
                yield! PartitionDistrib first subpart
    } 

and private PartitionDistrib (first:'T) (subpart:list<list<'T>>) : IEnumerable<list<list<'T>>> =
    seq {
        // Generate a sequence where 'first' appears at the front of each element of 'subpart' in turn.
        // For example, first=A, subpart=[[B];[C]] ==> { [[A;B];[C]; [[B];[A;C]] }.
        match subpart with
        | firstpart :: restparts ->
            yield (first :: firstpart) :: restparts
            if restparts <> [] then
                for distrib in PartitionDistrib first restparts do
                    yield firstpart :: distrib
        
        | _ -> failwith "Impossible case in PartitionDistrib."
    }