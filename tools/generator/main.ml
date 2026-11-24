(* stilt-gen: writes generated Stilt programs. *)

open Stilt_gen

(* Writes the files of a project to [dir], creating its directories. *)
let write_project dir files =
  let rec mkdir_p dir =
    if not (Sys.file_exists dir) then (
      mkdir_p (Filename.dirname dir);
      Sys.mkdir dir 0o755)
  in
  List.iter
    (fun (path, text) ->
      let path = Filename.concat dir path in
      mkdir_p (Filename.dirname path);
      Out_channel.with_open_text path (fun out ->
          Out_channel.output_string out text))
    files

(* Prints the program whose files [make] makes from [seed], each after a line
   that names it when there are several, or writes [count] of them, from
   consecutive seeds, to [dir]: seed_N.lt, or the directory seed_N of a
   directory program. *)
let generate_files make seed count dir =
  match dir with
  | None -> (
      match make seed with
      | [ (_, text) ] -> print_string text
      | files ->
          List.iter
            (fun (path, text) -> Printf.printf "// %s\n%s" path text)
            files)
  | Some dir ->
      (try Sys.mkdir dir 0o755
       with Sys_error _ when Sys.is_directory dir -> ());
      for seed = seed to seed + count - 1 do
        write_project dir (make seed)
      done

let generate make =
  generate_files (fun seed -> [ (Printf.sprintf "seed_%d.lt" seed, make seed) ])

open Cmdliner

let seed =
  Arg.(
    value & opt int 0
    & info [ "seed" ] ~docv:"N" ~doc:"The seed of the first program.")

let count =
  Arg.(
    value & opt int 1
    & info [ "count" ] ~docv:"N"
        ~doc:
          "How many programs to write, from consecutive seeds. Needs \
           $(b,--out).")

let out =
  Arg.(
    value
    & opt (some string) None
    & info [ "out" ] ~docv:"DIR"
        ~doc:
          "Write each program to $(docv)/seed_N.lt, or to the directory \
           $(docv)/seed_N when it has several files, instead of printing one.")

let mode name make doc =
  Cmd.v (Cmd.info name ~doc) Term.(const (generate make) $ seed $ count $ out)

(* Writes [count] csmith programs, from consecutive seeds, to [dir], as
   bundles of [size]: directory programs [dir]/seeds_A_to_B whose module
   [seed_N] is the program from seed N, and whose [main] runs each in turn. *)
let bundles size seed count dir =
  let write path text =
    Out_channel.with_open_text path (fun out ->
        Out_channel.output_string out text)
  in
  let mkdir dir =
    try Sys.mkdir dir 0o755 with Sys_error _ when Sys.is_directory dir -> ()
  in
  mkdir dir;
  let last = seed + count - 1 in
  let rec from first =
    if first <= last then (
      let seeds =
        List.init (min size (last - first + 1)) (fun i -> first + i)
      in
      let bundle =
        Filename.concat dir
          (Printf.sprintf "seeds_%d_to_%d" first
             (List.nth seeds (List.length seeds - 1)))
      in
      mkdir bundle;
      List.iter
        (fun s ->
          List.iter
            (fun (file, text) -> write (Filename.concat bundle file) text)
            (Csmith.module_files s))
        seeds;
      write (Filename.concat bundle "main.lt") (Csmith.bundle seeds);
      from (first + size))
  in
  from seed

let csmith =
  let bundle =
    Arg.(
      value
      & opt (some int) None
      & info [ "bundle" ] ~docv:"N"
          ~doc:
            "With $(b,--out), write the programs as directory programs of \
             $(docv) each, whose $(b,main) runs each program's in turn \
             (Csmith.bundle).")
  in
  let generate bundle seed count out =
    match (bundle, out) with
    | Some size, Some dir when size > 0 -> bundles size seed count dir
    | _ -> generate_files Csmith.files seed count out
  in
  Cmd.v
    (Cmd.info "csmith"
       ~doc:
         "Well-typed, terminating core programs that print what they compute, \
          with tests, doc examples and properties, which may fail.")
    Term.(const generate $ bundle $ seed $ count $ out)

let scale =
  let lines =
    Arg.(
      value & opt int 50_000
      & info [ "lines" ] ~docv:"N" ~doc:"The least number of lines to write.")
  in
  let dir =
    Arg.(
      required
      & opt (some string) None
      & info [ "out" ] ~docv:"DIR" ~doc:"The directory to write the project to.")
  in
  let doc =
    "A directory program of many modules that import one another, whose \
     modules are csmith programs without $(b,main)."
  in
  Cmd.v (Cmd.info "scale" ~doc)
    Term.(
      const (fun seed lines dir ->
          write_project dir (Scale.project ~seed ~lines))
      $ seed $ lines $ dir)

let mutation =
  let mistakes =
    Arg.(
      value & opt int 1
      & info [ "mistakes" ] ~docv:"N"
          ~doc:
            "How many mistakes to plant in each program, each in a different \
             function, or one in each function of a program that has fewer.")
  in
  let doc =
    "Csmith programs, without their tests, with planted mistakes, each \
     annotated with the diagnostic the Reference requires for it."
  in
  Cmd.v (Cmd.info "mutation" ~doc)
    Term.(
      const (fun count seed n out ->
          generate_files (Mutants.mutant ~count) seed n out)
      $ mistakes $ seed $ count $ out)

let syntax =
  let from =
    Arg.(
      non_empty & opt_all dir []
      & info [ "from" ] ~docv:"DIR"
          ~doc:"A directory whose .lt files are the programs to edit.")
  in
  let doc =
    "Programs with planted syntax errors, each an edit of the tokens of a \
     program under the $(b,--from) directories, which its seed picks."
  in
  Cmd.v (Cmd.info "syntax" ~doc)
    Term.(
      const (fun seed count out from ->
          generate
            (Syntax_errors.mutant (Syntax_errors.sources from))
            seed count out)
      $ seed $ count $ out $ from)

let () =
  exit
    (Cmd.eval
       (Cmd.group
          (Cmd.info "stilt-gen" ~doc:"Generates Stilt programs.")
          [
            csmith;
            mutation;
            mode "stress" Stress.program
              "Programs whose one function stresses inference: deep nesting, a \
               long method chain, a large match or if tree, or literals whose \
               type is known only at the end of the body.";
            scale;
            syntax;
          ]))
