#define left 0
#define right 1
#define boat 2
int goat_loc, cabbage_loc, wolf_loc;
bool illegal_state, goal_state;

init {
   goat_loc = left;
   cabbage_loc = left;
   wolf_loc = left;
   illegal_state = false;
   goal_state = false;
   gl_wl_cl:
      atomic{goat_loc = left; wolf_loc = left; cabbage_loc = left;}
      goto gb_wl_cl;
   gb_wl_cl:
      atomic{goat_loc = boat; wolf_loc = left; cabbage_loc = left;}
      goto gr_wl_cl;
   gr_wl_cl:
      atomic{goat_loc = right; wolf_loc = left; cabbage_loc = left;}
      goto gr_wl_cb;
   gr_wl_cb:
      atomic{goat_loc = right; wolf_loc = left; cabbage_loc = boat;}
      goto gb_wl_cr;
   gb_wl_cr:
      atomic{goat_loc = boat; wolf_loc = left; cabbage_loc = right;}
      goto gl_wb_cr;
   gl_wb_cr:
      atomic{goat_loc = left; wolf_loc = boat; cabbage_loc = right;}
      goto gl_wr_cr;
   gl_wr_cr:
      atomic{goat_loc = left; wolf_loc = right; cabbage_loc = right;}
      goto gb_wr_cr;
   gb_wr_cr:
      atomic{goat_loc = boat; wolf_loc = right; cabbage_loc = right;}
      goto gr_wr_cr;
   gr_wr_cr:
      atomic{goat_loc = right; wolf_loc = right; cabbage_loc = right; goal_state = true;}
      goto done;
   else_case:
      illegal_state = true;
   done:
   ltl goal {[] <> goal_state}
   ltl no_illegal {[] !illegal_state}
   ltl goat_cabbage_apart {[] !(goat_loc == left && cabbage_loc == left && wolf_loc != left)}
   ltl goat_cabbage_apart_r {[] !(goat_loc == right && cabbage_loc == right && wolf_loc != right)}
   ltl goat_wolf_apart {[] !(goat_loc == left && wolf_loc == left && cabbage_loc != left)}
   ltl goat_wolf_apart_r {[] !(goat_loc == right && wolf_loc == right && cabbage_loc != right)}
}
