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

module Env =
struct

  module type ARG =
  sig
    type t

    val name : string
    val doc  : string
    val default : t

    val get : unit -> t
  end

  module type BOOL   = ARG with type t = bool
  module type INT    = ARG with type t = int
  module type FLOAT  = ARG with type t = float
  module type STRING = ARG with type t = string

  module Generic
      (Arg : sig
         type t
         val name : string
         val doc  : string
         val default : t
         val of_string : string -> t
       end)
    : ARG with type t = Arg.t =
  struct
    include Arg
    let name = name
    let get () =
      try of_string (Sys.getenv name)
      with _ -> default
  end

  module Bool
      (Arg : sig
         val name : string
         val doc  : string
         val default : bool
       end) : BOOL =
  struct
    include Generic
        (struct
          include Arg
          type t = bool
          let of_string string = bool_of_string string
        end)
  end

  module Int
      (Arg : sig
         val name : string
         val doc  : string
         val default : int
       end) : INT =
  struct
    include Generic
        (struct
          include Arg
          type t = int
          let of_string string = int_of_string string
        end)
  end

  module Float
      (Arg : sig
         val name : string
         val doc  : string
         val default : float
       end) : FLOAT =
  struct
    include Generic
        (struct
          include Arg
          type t = float
          let of_string string = float_of_string string
        end)
  end

  module String
      (Arg : sig
         val name : string
         val doc  : string
         val default : string
       end) : STRING =
  struct
    include Generic
        (struct
          include Arg
          type t = string
          let of_string string = string
        end)
  end

end

(********************************************************************************)

module Coq =
struct

  module type ARG =
  sig
    type t

    val default : t
    val set : t -> unit
    val get : unit -> t
  end

  module type BOOL   = ARG with type t = bool
  module type INT    = ARG with type t = int
  module type FLOAT  = ARG with type t = float
  module type STRING = ARG with type t = string

  module Generic
      (Arg : sig
         type t
         val default : t
       end)
    : ARG with type t = Arg.t =
  struct
    include Arg
    let ref = ref default
    let set v  = ref := v
    let get () = !ref
  end

  module Int
      (Arg : sig
         val default : int
       end) : INT =
  struct
    include Generic
        (struct
          include Arg
          type t = int
        end)
  end

  module Float
      (Arg : sig
         val default : float
       end) : FLOAT =
  struct
    include Generic
        (struct
          include Arg
          type t = float
        end)
  end

  module String
      (Arg : sig
         val default : string
       end) : STRING =
  struct
    include Generic
        (struct
          include Arg
          type t = string
        end)
  end

  module type SET =
  sig
    type elt

    val clear  : unit -> unit
    val add    : elt -> unit
    val mem    : elt -> bool
    val remove : elt -> unit

    val elements : unit -> elt list
  end

  module Set
      (Ord : sig
         type t
         val compare : t -> t -> int
       end) =
  struct
    module S = Set.Make(Ord)
    type elt = S.elt

    let ref = ref S.empty
    let clear () = ref := S.empty
    let add v = ref := S.add v !ref
    let mem v = S.mem v !ref
    let remove v = ref := S.remove v !ref
    let elements () = S.elements !ref
  end

  module type MAP =
  sig
    type key
    type elt

    val clear  : unit -> unit
    val add    : key -> elt -> unit
    val find   : key -> elt option
    val remove : key -> unit

    val bindings : unit -> (key * elt) list
  end

  module Map
      (Ord : sig
         type t
         val compare : t -> t -> int
       end)
      (Elt : sig type t end) =
  struct
    module M = Map.Make(Ord)
    type key = M.key
    type elt = Elt.t

    let ref : elt M.t ref = ref M.empty
    let clear () = ref := M.empty
    let add k v = ref := M.add k v !ref
    let find k = M.find_opt k !ref
    let remove k = ref := M.remove k !ref
    let bindings () = M.bindings !ref
  end

end

(********************************************************************************)

module Info = Env.Bool
    (struct
      let name = "INFO"
      let doc  = "Enable or disable infos"
      let default = false
    end)

module Debug = Env.Bool
    (struct
      let name = "DEBUG"
      let doc  = "Enable or disable debugs"
      let default = false
    end)

module Warning = Env.Bool
    (struct
      let name = "WARNING"
      let doc  = "Enable or disable warnings"
      let default = true
    end)

module Error = Env.Bool
    (struct
      let name = "ERROR"
      let doc  = "Enable or disable errors"
      let default = true
    end)

module ArraySize = Coq.Int
    (struct
      let default = 16
    end)

module InlineDepth = Coq.Int
    (struct
      let default = 5
    end)

module InlinedConstants = Coq.Set(Names.KerName)
module InlinedRelations = Coq.Map(String)(Int)
module DestructRelations= Coq.Map(String)(Int)
