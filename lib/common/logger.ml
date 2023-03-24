open Vocab

type handle = {
    ch: out_channel;
    need_close: bool;
    debug: bool;
    start_time: float;
    mutable enabled: bool;
    mutable indent_depth: int;
}

type level = ERROR | INFO | DEBUG

let string_of_level (l: level): string = match l with
    | ERROR -> "ERROR"
    | INFO ->  "INFO "
    | DEBUG -> "DEBUG"
let _global_handle: handle option ref = ref None

let activate_global (handle: handle): unit = _global_handle := Some handle

let l_format_line (handle: handle) (cur_time: float) (l: level) (s: string): string list =
    let lines = BatString.split_on_string ~by:"\n" s in
    let (h,m,s) = diff_time_float_hms handle.start_time cur_time in
    BatList.map (fun line -> 
        Printf.sprintf "%03d:%02d:%02d %s | %s+ %s\n"
            h m s
            (string_of_level l)
            (BatString.init handle.indent_depth (fun _ -> ' '))
            line
        ) lines

let l_print (handle: handle) (level: level) (s: string): unit =
    if handle.enabled then begin
        l_format_line handle (Unix.time()) level s |> BatList.iter (output_string handle.ch)
    end

let l_error handle s = if handle.enabled then (l_print handle ERROR s; flush handle.ch)
let l_info handle s = if handle.enabled then (l_print handle INFO s; flush handle.ch)
let l_debug_lazy handle s_lazy = if handle.enabled && handle.debug then l_print handle DEBUG (s_lazy ())
let l_debug handle s = if handle.enabled && handle.debug then l_print handle DEBUG s

let l_close handle = if handle.need_close then close_out handle.ch
let l_flush handle = if handle.enabled then flush handle.ch

let l_with_increased_depth (handle: handle) (any_lazy: unit -> 'a): 'a =
    let preserve_depth = handle.indent_depth in
    try
        handle.indent_depth <- handle.indent_depth + 2;
        let result = any_lazy() in
        handle.indent_depth <- preserve_depth;
        result
    with exn -> begin
        handle.indent_depth <- preserve_depth;
        raise exn
    end

let _g(): handle =
    match !_global_handle with
    | Some h -> h
    | None -> invalid_arg "logger: global handle is not activated"

let g_error s = l_error (_g()) s
let g_info s = l_info (_g()) s
let g_debug_lazy s_lazy = l_debug_lazy (_g()) s_lazy
let g_debug s = l_debug (_g()) s

let g_error_f fmt = Printf.ksprintf g_error fmt
let g_info_f fmt = Printf.ksprintf g_info fmt
let g_debug_f fmt = Printf.ksprintf g_debug fmt
let g_in_debug_lazy (v_lazy: unit -> unit): unit =
    if ((_g()).debug) then v_lazy()

let g_close() = (* ignore None for convenience - just close anytime *)
    match !_global_handle with
    | Some h -> l_close h
    | None -> ()

let g_flush() = l_flush (_g())
let g_with_increased_depth (any_lazy: unit -> 'a): 'a =
    l_with_increased_depth (_g()) any_lazy

let null_handle: handle = {
    ch = stdout;
    need_close = false;
    debug = false;
    start_time = 0.0;
    enabled = false;
    indent_depth = 0;
}

let init_by_file (start_time: float) (debug: bool) (filename: string): handle =
    let handle = {ch = open_out filename;
        need_close = true;
        debug = debug;
        start_time = start_time;
        enabled=true;
        indent_depth = 0}
    in
    let tm = Unix.localtime start_time in
    output_string handle.ch (Printf.sprintf
        "HHH:MM:SS TYPE  | + Logger initialized with file %s at %02d-%02d-%02d.%02d:%02d:%02d\n"
        filename
        (tm.tm_year mod 100) (tm.tm_mon + 1) tm.tm_mday
        tm.tm_hour tm.tm_min tm.tm_sec);
    handle

let init_by_channel (start_time: float) (debug: bool) (ch: out_channel): handle =
    let handle = {ch = ch;
        need_close = false;
        debug = debug;
        start_time = start_time;
        enabled=true;
        indent_depth = 0;}
    in
    let tm = Unix.localtime start_time in
    output_string handle.ch (Printf.sprintf
        "HHH:MM:SS TYPE  | + Logger initialized with given channel at %02d-%02d-%02d.%02d:%02d:%02d\n"
        (tm.tm_year mod 100) (tm.tm_mon + 1) tm.tm_mday
        tm.tm_hour tm.tm_min tm.tm_sec);
    handle

type periodic_reporter = {
    handle: handle;
    period_ms: int;
    mutable last_printed: float;
}

let create_g_periodic_logger(ms: int): periodic_reporter = {
    handle = _g();
    period_ms = ms;
    last_printed = Unix.gettimeofday();
}

let info_period (p: periodic_reporter) (s_lazy: unit -> string): unit =
    let cur_time = Unix.gettimeofday() in
    if (cur_time -. p.last_printed) > float_of_int p.period_ms /. 1000. then begin
        p.last_printed <- cur_time;
        l_info p.handle (s_lazy());
    end