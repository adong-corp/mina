open Core_kernel

type remote_error = {node_id: string; error_message: Logger.Message.t}

(* NB: equality on internal errors ignores timestamp *)
type internal_error =
  { occurrence_time: Time.t sexp_opaque
        [@equal fun _ _ -> true] [@compare fun _ _ -> 0]
  ; error: Error.t
        [@equal
          fun a b ->
            String.equal (Error.to_string_hum a) (Error.to_string_hum b)]
        [@compare
          fun a b ->
            String.compare (Error.to_string_hum a) (Error.to_string_hum b)] }
[@@deriving eq, sexp, compare]

type t = Remote_error of remote_error | Internal_error of internal_error

let raw_internal_error error = {occurrence_time= Time.now (); error}

let internal_error error = Internal_error (raw_internal_error error)

let internal_error_from_raw error = Internal_error error

let to_string = function
  | Remote_error {node_id; error_message} ->
      Printf.sprintf "[%s] %s: %s"
        (Time.to_string error_message.timestamp)
        node_id
        (Yojson.Safe.to_string (Logger.Message.to_yojson error_message))
  | Internal_error {occurrence_time; error} ->
      Printf.sprintf "[%s] test_executive: %s"
        (Time.to_string occurrence_time)
        (Error.to_string_hum error)

let occurrence_time_of_internal_error {occurrence_time; _} = occurrence_time

let occurrence_time = function
  | Remote_error {error_message; _} ->
      error_message.timestamp
  | Internal_error {occurrence_time; _} ->
      occurrence_time

let compare_time a b = Time.compare (occurrence_time a) (occurrence_time b)

module TimeMap = Map.Make_using_comparator (struct
  include Time

  let sexp_of_t time =
    time
    |> Time.to_span_since_epoch
    |> Time.Span.to_ns
    |> Float.sexp_of_t

  let t_of_sexp sexp =
    sexp
    |> Float.t_of_sexp
    |> Time.Span.of_ns
    |> Time.of_span_since_epoch
end)

(* currently a flat set of contexts mapped to errors, but perhaps a tree (for nested contexts) is better *)
module Error_accumulator = struct
  (* THOUGHT: every error needs a time *)
  (* store errors per context in a map indexed by time; will solve a lot of problems *)

  (* TODO: UPDATEME *)
  (** An error accumulator accumulates and organizes errors based on contexts.
   *  Errors can be accumulated within an unspecified context, and can then
   *  later be upgraded into a specific context. The error accumulator tracks
   *  an ordered set of contexts, ordered by the time at which the context was 
   *  introduced into the accumulator. For performance reasons, these contexts
   *  are stored from most recent to least recent introduction.
   *
   *  INVARIANT: List.for_all (String.Map.keys contextualized_errors) (List.mem contexts)
   *)

  type 'error t =
    { from_current_context: 'error list
    ; contextualized_errors: 'error list TimeMap.t String.Map.t }
  [@@deriving eq, sexp_of, compare]

  let record_errors map context new_errors ~time_of_error =
    String.Map.update map context ~f:(fun errors_opt ->
      let errors = Option.value errors_opt ~default:TimeMap.empty in
      List.fold new_errors ~init:errors ~f:(fun acc error ->
        TimeMap.add_multi acc ~key:(time_of_error error) ~data:error))

  let empty =
    {from_current_context= []; contextualized_errors= String.Map.empty}

  let error_count {from_current_context; contextualized_errors} =
    List.length from_current_context + String.Map.length contextualized_errors

  let all_errors {from_current_context; contextualized_errors} =
    from_current_context
    @ List.concat (List.bind (String.Map.data contextualized_errors) ~f:TimeMap.data)

  let contextualize' context {from_current_context; contextualized_errors} ~time_of_error =
    { empty with
      contextualized_errors=
        record_errors contextualized_errors context from_current_context ~time_of_error }

  let contextualize = contextualize' ~time_of_error:occurrence_time

  let singleton x = {empty with from_current_context= [x]}

  let of_context_free_list ls = {empty with from_current_context= ls}

  let of_contextualized_list' context ls ~time_of_error =
    { empty with
      contextualized_errors= record_errors String.Map.empty context ls ~time_of_error }

  let of_contextualized_list = of_contextualized_list' ~time_of_error:occurrence_time

  let add t error =
    {t with from_current_context= error :: t.from_current_context}

  let map {from_current_context; contextualized_errors} ~f =
    { from_current_context= List.map from_current_context ~f
    ; contextualized_errors=
        String.Map.map contextualized_errors ~f:(TimeMap.map ~f:(List.map ~f)) }

  let iter_contexts {from_current_context; contextualized_errors} ~f =
    let contexts_by_time =
      contextualized_errors
      |> String.Map.to_alist
      |> List.map ~f:(fun (ctx, errors) ->
          let earliest_error_time =
            errors
            |> TimeMap.keys
            |> List.min_elt ~compare:Time.compare
               (* there should always be at least one error in these lists *)
            |> Option.value_exn
          in
          (earliest_error_time, ctx))
      |> TimeMap.of_alist_exn
    in
    let sorted_errors_by_context =
      String.Map.map contextualized_errors ~f:(fun errors_by_time ->
        List.concat (TimeMap.data errors_by_time))
    in
    f None from_current_context ;
    TimeMap.iter contexts_by_time ~f:(fun context ->
      f (Some context) (String.Map.find_exn sorted_errors_by_context context))

  let merge a b =
    let from_current_context =
      a.from_current_context @ b.from_current_context
    in
    let contextualized_errors =
      let merge_maps
          (type a key comparator_witness)
          (map_a : (key, a, comparator_witness) Map.t)
          (map_b : (key, a, comparator_witness) Map.t)
          ~(resolve_conflict: a -> a -> a)
        : (key, a, comparator_witness) Map.t
        = Map.fold map_b ~init:map_a ~f:(fun ~key ~data acc ->
            Map.update acc key ~f:(function
              | None -> data
              | Some data' -> resolve_conflict data' data))
      in
      merge_maps a.contextualized_errors b.contextualized_errors
        ~resolve_conflict:(merge_maps ~resolve_conflict:(@))
    in
    {from_current_context; contextualized_errors}

  let combine = List.fold ~init:empty ~f:merge

  let partition {from_current_context; contextualized_errors} ~f =
    let from_current_context_a, from_current_context_b =
      List.partition_tf from_current_context ~f
    in
    let contextualized_errors_a, contextualized_errors_b =
      let partition_map
          (type key a w)
          (cmp : (key, w) Map.comparator)
          (map : (key, a, w) Map.t)
          ~(f : (a -> a * a))
        : (key, a, w) Map.t * (key, a, w) Map.t
        = Map.fold map ~init:(Map.empty cmp, Map.empty cmp) ~f:(fun ~key ~data (left, right) ->
            let (l, r) = f data in
            (Map.add_exn left ~key ~data:l, Map.add_exn right ~key ~data:r))
      in
      partition_map (module String) contextualized_errors ~f:(fun errors_by_time ->
        partition_map (module Time) errors_by_time ~f:(List.partition_tf ~f))
    in
    let a =
      { from_current_context= from_current_context_a
      ; contextualized_errors= contextualized_errors_a }
    in
    let b =
      { from_current_context= from_current_context_b
      ; contextualized_errors= contextualized_errors_b }
    in
    (a, b)
end

module Set = struct
  type nonrec t =
    {soft_errors: t Error_accumulator.t; hard_errors: t Error_accumulator.t}

  let empty =
    {soft_errors= Error_accumulator.empty; hard_errors= Error_accumulator.empty}

  let all_errors {soft_errors; hard_errors} =
    Error_accumulator.merge soft_errors hard_errors

  let soft_singleton err =
    {empty with soft_errors= Error_accumulator.singleton err}

  let hard_singleton err =
    {empty with hard_errors= Error_accumulator.singleton err}

  let of_soft_or_error = function
    | Ok () ->
        empty
    | Error err ->
        soft_singleton (internal_error err)

  let of_hard_or_error = function
    | Ok () ->
        empty
    | Error err ->
        hard_singleton (internal_error err)

  let add_soft err t =
    {t with soft_errors= Error_accumulator.add t.soft_errors err}

  let add_hard err t =
    {t with hard_errors= Error_accumulator.add t.soft_errors err}

  let merge a b =
    { soft_errors= Error_accumulator.merge a.soft_errors b.soft_errors
    ; hard_errors= Error_accumulator.merge a.hard_errors b.hard_errors }

  let combine = List.fold_left ~init:empty ~f:merge

  let partition {soft_errors; hard_errors} ~f =
    let soft_errors_a, soft_errors_b =
      Error_accumulator.partition soft_errors ~f
    in
    let hard_errors_a, hard_errors_b =
      Error_accumulator.partition hard_errors ~f
    in
    let a = {soft_errors= soft_errors_a; hard_errors= hard_errors_a} in
    let b = {soft_errors= soft_errors_b; hard_errors= hard_errors_b} in
    (a, b)
end
