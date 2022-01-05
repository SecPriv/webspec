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

let () = Format.set_max_indent (Format.get_margin () / 2)
let () = Format.set_max_boxes max_int

type ('a,'b) msg = (('a, Format.formatter, unit, 'b) format4 -> 'a) -> 'b

module type SRC =
sig
  val name : string

  val info    : unit -> bool
  val debug   : unit -> bool
  val warning : unit -> bool
  val error   : unit -> bool
end

module type LOG =
sig
  val info    : ('a,unit) msg -> unit
  val debug   : ('a,unit) msg -> unit
  val warning : ('a,unit) msg -> unit
  val error   : ('a,unit) msg -> unit

  module Verbose :
  sig
    type ('a,'b) verbose =
      head:('a,unit) msg ->
      body:('b,unit) msg ->
      unit

    val info    : ('a,'b) verbose
    val debug   : ('a,'b) verbose
    val warning : ('a,'b) verbose
    val error   : ('a,'b) verbose
  end
end

let pp_time fmt () =
  let time = Unix.gettimeofday () in
  let local = Unix.localtime time in
  Format.fprintf fmt "%02i:%02i:%06.3f"
    local.Unix.tm_hour
    local.Unix.tm_min
    (Float.of_int local.Unix.tm_sec +. time -. (Float.round time))

type level = Info | Debug | Warning | Error

let pp_level fmt = function
  | Info    -> Format.fprintf fmt "info"
  | Debug   -> Format.fprintf fmt "debug"
  | Warning -> Format.fprintf fmt "warning"
  | Error   -> Format.fprintf fmt "error"

type channel = {
  fmt : Format.formatter;
  lvl : level;
  src : string;
  enable : unit -> bool;
}

let pp_channel fmt chn =
  Format.fprintf fmt "[%a][%a][%s]"
    pp_time () pp_level chn.lvl chn.src

let log chan msg =
  if chan.enable () then
    msg @@ fun fmt ->
    Format.kfprintf
      (fun chan ->
         Format.kfprintf
           (fun chan ->
              Format.fprintf chan "\n%!")
           chan fmt)
      chan.fmt "%a " pp_channel chan

let sep = String.make 72 '-'

let verbose chan ~head ~body =
  if chan.enable () then
    head @@ fun fmt ->
    Format.kfprintf
      (fun chan ->
         Format.kfprintf
           (fun chan ->
              body @@ fun fmt ->
              Format.kfprintf
                (fun chan ->
                   Format.kfprintf
                     (fun chan ->
                        Format.fprintf chan "\n%s\n%!" sep)
                     chan fmt)
                chan "\n%s\n%!" sep)
           chan fmt)
      chan.fmt "%a " pp_channel chan

module Make (Src : SRC) : LOG =
struct

  let info_channel = {
    fmt = Format.err_formatter;
    lvl = Info;
    src = Src.name;
    enable = Src.info;
  }

  let debug_channel = {
    fmt = Format.err_formatter;
    lvl = Debug;
    src = Src.name;
    enable = Src.debug;
  }

  let warning_channel = {
    fmt = Format.err_formatter;
    lvl = Warning;
    src = Src.name;
    enable = Src.warning;
  }

  let error_channel = {
    fmt = Format.err_formatter;
    lvl = Error;
    src = Src.name;
    enable = Src.error;
  }

  let info    msg = log info_channel    msg
  let debug   msg = log debug_channel   msg
  let warning msg = log warning_channel msg
  let error   msg = log error_channel   msg

  module Verbose =
  struct
    type ('a,'b) verbose =
      head:('a, unit) msg ->
      body:('b, unit) msg ->
      unit

    let info    ~head ~body = verbose info_channel    ~head ~body
    let debug   ~head ~body = verbose debug_channel   ~head ~body
    let warning ~head ~body = verbose warning_channel ~head ~body
    let error   ~head ~body = verbose error_channel   ~head ~body
  end
end

module Default (Src : sig val name : string end) =
  Make
    (struct
      let name = Src.name
      let info    () = Config.Info.get ()
      let debug   () = Config.Debug.get ()
      let warning () = Config.Warning.get ()
      let error   () = Config.Error.get ()
    end)
