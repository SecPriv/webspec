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


module type S =
sig
  val s_response : States.VerifierState.t -> int -> string
  val s_request : States.VerifierState.t -> int -> string
  (* RoundTrip-related functions*)
end

module ServiceWorker : S =
struct
  
  let s_response (st : States.VerifierState.t) (rp_idx : int) : string = 
    let trace = Option.get st.trace in
    List.iter (fun (i, el) -> print_endline (Printf.sprintf "%d: %s" i @@ Types.Response.show el)) trace.global.responses ;
    List.iter (fun (i, el) -> print_endline (Printf.sprintf "%d: %s" i @@ Types.Request.show el)) trace.global.requests ;
    print_endline ("RESP INDEX" ^ (string_of_int rp_idx)) ;
    let resp = Model.Array.select trace.global.responses rp_idx in

    print_endline @@ Types.Response.show resp ; 

    let status = Types.ResponseCode.show resp.rp_code in 
    let headers = Types.ResponseHeaders.to_yojson (
      States.VerifierState.translate_response_headers st resp.rp_headers )
    in
    print_endline (Types.ResponseHeaders.show (States.VerifierState.translate_response_headers st resp.rp_headers) );

    let content = 
      match resp.rp_content with 
      | Some (ContentElementImage (url)) -> ( print_endline "TODO: ADD IMAGE AS RP CONTENT" ; Types.URL.show (States.VerifierState.translate_url st url) )
      | Some (ContentElementScript (script)) -> ( 
        let path = States.VerifierState.find_script_by_src st script.script_src in 
        let path = try Option.get path with Invalid_argument _ -> failwith "[serviceworker.ml] Script not found" in
        let sc = Types.NestedDOMPath.Map.find path st.scripts in 
        sc.repr

        )
      | Some (ContentElementFrame (_frame, html)) -> ( 
          Html.Translator.html_to_string st html None
        )
      | Some (ContentElementHTML (html)) -> ( 
          Html.Translator.html_to_string st html  None
        )
      | _ -> ""
    in

    Printf.sprintf "new Response('%s', {status: '%s', headers:%s})"
      (content)
      (status)
      (Yojson.Safe.pretty_to_string headers)

  let s_request (st : States.VerifierState.t) (rq_idx : int) : string =
    let trace = Option.get st.trace in
    let req = Model.Array.select trace.global.requests rq_idx in
 
    let url = States.VerifierState.translate_url st req.rq_url in
    let url_string = Types.URL.show url in

    let mthd = Types.RequestMethod.show req.rq_method in 
    let headers = Types.RequestHeaders.to_yojson (
      States.VerifierState.translate_request_headers 
      st 
      req.rq_headers )
    in

    Printf.sprintf "new Request('%s', {method: '%s', headers:%s})"
      (url_string)
      (mthd)
      (Yojson.Safe.pretty_to_string headers)

end
