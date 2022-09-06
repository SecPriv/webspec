(********************************************************************************)
(*  Copyright (c) 2022 Pedro Bernardo                                                *)
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

module type Visitor =
sig
  type t
  val request_handler :  t -> Model.Browser.coq_Emitter -> Model.Browser.coq_Request -> int -> Types.State.t option -> t
  val response_handler : t -> Model.Browser.coq_Response -> int -> t
  val url_source_handler : t -> Model.Browser.coq_URL -> Model.Browser.coq_HTMLElement option -> t 
  val url_handler : t -> Model.Browser.coq_URL -> t
  val domupdate_handler : t -> Types.NestedDOMPath.t -> t 
  val default_handler : t -> Model.Browser.coq_Event -> t
  val handle : t -> (Types.Event.t * Types.State.t option) -> t
end

module Preprocessor : Visitor with type t = States.VerifierState.t
module ResponseGenerator : Visitor with type t = States.VerifierState.t
