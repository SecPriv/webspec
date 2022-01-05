(********************************************************************************)
(*  Copyright (c) 2021 Benjamin Farinier                                        *)
(*                                                                              *)
(*  Permission is hereby granted, free of charge, to any person obtaining a     *)
(*  copy of this software and associated documentation files (the "Software"),  *)
(*  to deal in the Software without restriction, including without limitation   *)
(*  the rights to use, copy, modify, merge, publish, distribute, sublicense,    *)
(*  and/or sell copies of the Software, and to permit persons to whom the       *)
(*  Software is furnished to do so, subject to the following conditions:        *)
(*                                                                              *)
(*  The above copyright notice and this permission notice shall be included in  *)
(*  all copies or substantial portions of the Software.                         *)
(*                                                                              *)
(*  THE SOFTWARE IS PROVIDED "AS IS", WITHOUT WARRANTY OF ANY KIND, EXPRESS OR  *)
(*  IMPLIED, INCLUDING BUT NOT LIMITED TO THE WARRANTIES OF MERCHANTABILITY,    *)
(*  FITNESS FOR A PARTICULAR PURPOSE AND NONINFRINGEMENT. IN NO EVENT SHALL     *)
(*  THE AUTHORS OR COPYRIGHT HOLDERS BE LIABLE FOR ANY CLAIM, DAMAGES OR OTHER  *)
(*  LIABILITY, WHETHER IN AN ACTION OF CONTRACT, TORT OR OTHERWISE, ARISING     *)
(*  FROM, OUT OF OR IN CONNECTION WITH THE SOFTWARE OR THE USE OR OTHER         *)
(*  DEALINGS IN THE SOFTWARE.                                                   *)
(*                                                                              *)
(********************************************************************************)


type 'a t = ('a, exn) result


module Monad =
struct

  let (>>=) r f = match r with Ok v -> f v | Error _ as e -> e

  let (>>|) r f = match r with Ok v -> Ok (f v) | Error _ as e -> e


  let return = function
    | Error exn -> raise exn
    | Ok x -> x


  let failure msg =
    Error (Failure (msg @@ fun fmt -> Format.sprintf fmt))

end


module Option =
struct

  let map f option =
    match option with
    | None -> Ok None
    | Some x ->
      match f x with
      | Ok x -> Ok (Some x)
      | Error _ as e -> e

end


module Array =
struct

  let fold_left f acc array =
    match acc with
    | Ok acc ->
      (try
         Ok
           (Array.fold_left
              (fun acc x ->
                 match f acc x with
                 | Ok v -> v
                 | Error exn -> raise exn)
              acc array)
       with exn -> Error exn)
    | Error _ as result -> result

  let fold_right f array acc =
    match acc with
    | Ok acc ->
      (try
         Ok
           (Array.fold_right
              (fun x acc ->
                 match f x acc with
                 | Ok v -> v
                 | Error exn -> raise exn)
              array acc)
       with exn -> Error exn)
    | Error _ as result -> result

  let map f array =
    try
      Ok (Array.map
            (fun x -> match f x with
               | Ok v -> v
               | Error exn -> raise exn)
            array)
    with exn -> Error exn

  let map2 f array1 array2 =
    try
      Ok (Array.map2
            (fun x y -> match f x y with
               | Ok v -> v
               | Error exn -> raise exn)
            array1 array2)
    with exn -> Error exn

end


module List =
struct

  let fold_left f acc list =
    match acc with
    | Ok acc ->
      (try
         Ok
           (List.fold_left
              (fun acc x ->
                 match f acc x with
                 | Ok v -> v
                 | Error exn -> raise exn)
              acc list)
       with exn -> Error exn)
    | Error _ as result -> result

  let fold_right f list acc =
    match acc with
    | Ok acc ->
      (try
         Ok
           (List.fold_right
              (fun x acc ->
                 match f x acc with
                 | Ok v -> v
                 | Error exn -> raise exn)
              list acc)
       with exn -> Error exn)
    | Error _ as result -> result

  let map f list =
    try
      Ok (List.map
            (fun x -> match f x with
               | Ok v -> v
               | Error exn -> raise exn)
            list)
    with exn -> Error exn

  let map2 f list1 list2 =
    try
      Ok (List.map2
            (fun x y -> match f x y with
               | Ok v -> v
               | Error exn -> raise exn)
            list1 list2)
    with exn -> Error exn

  let filter_map f list =
    try
      Ok (List.filter_map
            (fun x -> match f x with
               | Ok v -> v
               | Error exn -> raise exn)
            list)
    with exn -> Error exn
end

