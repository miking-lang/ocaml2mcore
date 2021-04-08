let rec print_list = function
  | [] -> ()
  | x :: xs ->
    print_int x;
    print_list xs

let l = List.init 10 (fun x -> x)

let l, u = List.partition (fun x -> x > 4) l

let _ =
  print_list l;
  print_endline "";
  print_list u
