
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
  type t

  val html_to_string : t -> Types.HTML.t -> string list option -> string
end

module Translator : S with type t = States.VerifierState.t = 
struct
  type t = States.VerifierState.t

  let html_element_acc (st : t) (acc : string list) (elm : (int * Types.HTMLElement.t option)) : string list = 
    match elm with 
    | (_, None) -> acc
    | (_, Some(el)) -> (
      let htmel = 
        match el with 
        | HTMLImage (url) -> (
          Printf.sprintf "<img src='%s' />" 
          (Types.URL.show (States.VerifierState.translate_url st url))
        )
        | HTMLScript (url) -> (
          match url with 
          | { url_protocol=ProtocolData ; url_host=_ ; url_port=_ ; url_path=Coq_url_path_data(nonce, idx) } -> (
            let trace = Option.get st.trace in
            let script_src = 
              match Model.Array.select trace.global.data_urls idx with 
              | ContentElementScript (sc) -> sc.script_src
              | _ -> failwith "[html_element_acc] HTML script using data url is not pointing to a script content element"
            in
            let scr_path = try Option.get @@ States.VerifierState.find_script_by_src st script_src with 
              Invalid_argument _ -> failwith "[html_element_acc] did not find script" in
            
            let scr = try Types.NestedDOMPath.Map.find scr_path st.scripts with
              Invalid_argument _ -> failwith "[html_element_acc] did not find script (internal)" in

            Base64.encode_exn scr.repr |> 
            Printf.sprintf "data:text/javascript,eval(atob('%s'))" |>
            Printf.sprintf "<script src=\"%s\"></script>"

          )
          | _ -> (
            Printf.sprintf "<script src='%s' ></script>" 
            (Types.URL.show (States.VerifierState.translate_url st url))
          )
        )
        | HTMLForm (mthd, url) -> (
          Printf.sprintf "<form action='%s' method='%s' ></form>" 
          (Types.URL.show (States.VerifierState.translate_url st url)) 
          (Types.RequestMethod.show mthd)
        )
        | HTMLFrame (url) -> (
          Printf.sprintf "<iframe src='%s'></iframe>"
          (Types.URL.show (States.VerifierState.translate_url st url))
        )
      in 
    acc @ [htmel]
    )

  let html_csp_check (urls : string list option) : string = 
    match urls with 
    | Some(l) -> (
      Printf.sprintf "<head>%s</head>" @@
      List.fold_left (fun acc x -> Printf.sprintf "%s<script src='%s' defer ></script>" acc x) "" l
    )
    | None -> ""

  let html_to_string (st : t) (html : Types.HTML.t) (csp_urls : string list option): string = 
    ignore (
      match csp_urls with 
      | Some(l) -> List.iter print_endline l
      | _ -> ()
    ) ;
    let sorted_body = (List.sort (fun (k1, _v1) (k2, _v2) -> k1 - k2) html.html_body) in 
    let body = String.concat "" (List.fold_left (html_element_acc st) [] sorted_body) in
    Printf.sprintf "<!DOCTYPE html><html>%s<body>%s</body></html>" (html_csp_check csp_urls) body 

end
