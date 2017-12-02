%
% Catan board generator in MiniZinc.
%
% This is not a general model
% 

% """
% A specification is a hexagonial matrix of terrain pieces. Each terrain piece has a terrain type and
% a number. The sum over two D6 dices (1-6 dices) indicates what terrain piece(s) produces resources;
% the terrain pieces with the same number as the sum will produce the resource type of its terrain type.
% """
% 
% E.g.
% Given the six terrain types with the corresponding enumeration, resource, and their quantity:
%   Tile:    |Enum:|Resource:|Quantity:
% ----------- ----- --------- -----------
%   Fields   |   1 |   Grain |        4
%   Forest   |   2 |   Wood  |        4
%   Pasture  |   3 |   Wool  |        4
%   Mountains|   4 |   Ore   |        3
%   Hills    |   5 |   Brick |        3
%   Desert   |   6 |   None  |        1
% ----------- ----- --------- -----------
%
% And the numbers with their respecitve quantity and the probability of rolling such number wih a pair of 6 sided dices
%   Number:|Quantity:|Probability:
% --------- --------- --------------
%         2|        1|        1/36
%         3|        2|        2/36
%         4|        2|        3/36
%         5|        2|        4/36
%         6|        2|        5/36
%         8|        2|        5/36
%         9|        2|        4/36
%        10|        2|        3/36
%        11|        2|        2/36
%        12|        1|        1/36
% --------- --------- --------------
%
%         .'.   .'.   .'. 
%       .´  1`.´  3`.´  2`.
%       |N:  2|N:  5|N: 11|
%      .'.   .'.   .'.   .'. 
%    .´  3`.´  2`.´  1`.´  5`.
%    |N:  4|N:  6|N:  9|N:  3|
%   .'.   .'.   .'.   .'.   .'. 
% .´  2`.´  1`.´  6`.´  2`.´  4`.
% |N: 12|N:  8|N:  0|N:  8|N: 10|
% '.   .'.   .'.   .'.   .'.   .'
%   `.´  3`.´  5`.´  4`.´  5`.´
%    |N:  9|N:  5|N:  6|N:  4|
%    '.   .'.   .'.   .'.   .'
%      `.´  4`.´  3`.´  1`.´
%       |N: 11|N:  3|N: 10|
%       '.   .'.   .'.   .'
%         `.´   `.´   `.´
%

include "globals.mzn";

int: rowCount = 5; % rows
int: colCount = 5; % columns

% encoding: -1 for unknown, >= 0 for number of mines in the neighbourhood
% encoding:
%   1: Fields    (Grain)
%   2: Forest    (Wood)
%   3: Pasture   (Wool)
%   4: Mountains (Ore)
%   5: Hills     (Brick)
%   6: Desert    (None)
%
% Number encoding:
% 12 =  1
% 11 =  2
% 10 =  3
%  9 =  4
%  8 =  5
%  7 =  0
%  6 = -5
%  5 = -4
%  4 = -3
%  3 = -2
%  2 = -1

array[1..10] of int: allotments      = array1d(1..10, [-1,-2,-3,-4,-5, 5, 4, 3, 2, 1]);
array[1..10] of int: allotmentsCount = array1d(1..10, [ 1, 2, 2, 2, 2, 2, 2, 2, 2, 1]);
array[1..6] of int: fieldTypesCount  = array1d(1..6,  [4, 4, 4, 3, 3, 1]);
array[1..rowCount, 1..colCount] of int: active = array2d(1..rowCount,
                                                         1..colCount,
                                                         [
                                                            0,1,1,1,0,
                                                            1,1,1,1,0,
                                                            1,1,1,1,1,
                                                            1,1,1,1,0,
                                                            0,1,1,1,0
                                                         ]);

array[1..rowCount, 1..colCount] of var 0..6: fieldType;
array[1..rowCount, 1..colCount] of var -5..5: fieldAllotment;
array[1..rowCount, 1..colCount] of var 0..106: fieldTypeAllotment;
array[1..rowCount, 1..colCount] of var 0..5: weightedFieldAllotment;
array[1..18] of var 12..56: neighbourhoodAllotmentScore;
array[1..5] of var 0..56: fieldTypeScore; % Ignore Desert


constraint
    fieldType[3,3] == 6 /\ % Desert
    fieldAllotment[1,2] < 0 /\ % Symmetry Breaking 1
    fieldAllotment[1,3] > 0 /\ % Symmetry Breaking 1
    (fieldAllotment[2,1] > 0 \/ fieldAllotment[2,1] = fieldAllotment[1,3]) /\ % Symmetry Breaking 1
%    /\ (fieldType[1,2] < fieldType[1,4] \/ (fieldType[1,2] == fieldType[1,4] /\ fieldAllotment[1,2] <= fieldAllotment[1,4])) % Symmetry
%    /\ (fieldType[1,2] < fieldType[3,1] \/ (fieldType[1,2] == fieldType[3,1] /\ fieldAllotment[1,2] <= fieldAllotment[3,1])) % Symmetry
%    /\ (fieldType[1,2] < fieldType[3,5] \/ (fieldType[1,2] == fieldType[3,5] /\ fieldAllotment[1,2] <= fieldAllotment[3,5])) % Symmetry
%    /\ (fieldType[1,2] < fieldType[5,2] \/ (fieldType[1,2] == fieldType[5,2] /\ fieldAllotment[1,2] <= fieldAllotment[5,2])) % Symmetry
%    /\ (fieldType[1,2] < fieldType[5,4] \/ (fieldType[1,2] == fieldType[5,4] /\ fieldAllotment[1,2] <= fieldAllotment[5,4])) % Symmetry
%    /\ (fieldType[1,2] == 1 \/ fieldType[1,2] == 4 \/ fieldType[1,2] == 6)
%    /\ (fieldType[2,2] != 3)
%    /\
    fieldType[1, 3] != 1 /\ fieldType[1, 4] != 1 /\ % Grain harbor
    fieldType[1, 4] != 4 /\ fieldType[2, 4] != 4 /\ % Ore Harbor
    fieldType[2, 1] != 2 /\ fieldType[3, 1] != 2 /\ % Wood Harbor
    fieldType[3, 1] != 5 /\ fieldType[4, 1] != 5 /\ % Brick Harbor
    fieldType[4, 4] != 4 /\ fieldType[5, 4] != 3 /\ % Wool Harbor
  
    (weightedFieldAllotment[2, 2] = 5 \/ weightedFieldAllotment[2, 3] = 5) /\
    (weightedFieldAllotment[3, 2] = 5 \/ weightedFieldAllotment[3, 4] = 5) /\
    (weightedFieldAllotment[4, 2] = 5 \/ weightedFieldAllotment[4, 3] = 5) /\

    forall(row in 1..rowCount, col in 1..colCount) (
      if active[row, col] = 0 then
        fieldType[row, col] == 0 /\
        fieldAllotment[row, col] == 0 /\
        weightedFieldAllotment[row, col] == 0 /\
        fieldTypeAllotment[row, col] == 0
      else
        weightedFieldAllotment[row, col] == abs(fieldAllotment[row, col]) /\
        fieldType[row, col] > 0 /\
        if fieldType[row, col] == 6 then 
          fieldAllotment[row, col] == 0 /\
          fieldTypeAllotment[row, col] == 0
        else 
          fieldAllotment[row, col] != 0 /\
          fieldTypeAllotment[row, col] = (10 * (5 +fieldAllotment[row, col])) + fieldType[row, col]
        endif
      endif
     )
     /\
%0,1,1,1,0,
% 1,1,1,1,0,
%1,1,1,1,1,
% 1,1,1,1,0,
%0,1,1,1,0
    % Ensure that field types are somewhat spread out evenly
    % Field types with a field count of 4
    forall(f in 1..3) (
      % Top-left most section
      count([fieldType[1, 2], fieldType[1, 3], fieldType[2, 1], fieldType[2, 2], fieldType[3, 1], fieldType[3, 2]], f) >= 1 /\
      % Top-right most section
      count([fieldType[1, 3], fieldType[1, 4], fieldType[2, 3], fieldType[2, 4], fieldType[3, 4], fieldType[3, 5]], 1) >= 1 /\
      % Bottom-left most section
      count([fieldType[3, 1], fieldType[3, 2], fieldType[4, 1], fieldType[4, 2], fieldType[5, 2], fieldType[5, 3]], 1) >= 1 /\
      % Bottom-right most section
      count([fieldType[3, 4], fieldType[3, 5], fieldType[4, 3], fieldType[4, 4], fieldType[5, 3], fieldType[5, 4]], 1) >= 1
    ) /\
    % Field types with a field count of 3     
    forall(f in 2..3) (      
      % Diagonal from [1, 4] to [3, 5]
      count([fieldType[1, 4], fieldType[2, 4], fieldType[3, 5]], f) <= 1 /\
      % Diagonal from [3, 1] to [5, 2]
      count([fieldType[3, 1], fieldType[4, 1], fieldType[5, 2]], f) <= 1 /\
      % Diagonal from [3, 5] to [5, 2]
      count([fieldType[3, 5], fieldType[4, 4], fieldType[5, 4]], f) <= 1 /\
      % Row from [5,2] to [5,4]
      count([fieldType[5, 2], fieldType[5, 3], fieldType[5, 4]], f) <= 1 /\
      % Row from [1, 2] to [1, 4]
      count([fieldType[1, 2], fieldType[1, 3], fieldType[1, 4]], f) <= 1 /\
      % Diagonal from [1, 2] to [3, 1]
      count([fieldType[1, 2], fieldType[2, 1], fieldType[3, 1]], f) <= 1 /\
      % Diagonal from [1, 4] to [3, 5]
      count([fieldType[1, 4], fieldType[2, 4], fieldType[3, 5]], f) <= 1 /\
      % Diagonal from [3, 1] to [5, 2]
      count([fieldType[3, 1], fieldType[4, 1], fieldType[5, 2]], f) <= 1 /\
      % Diagonal from [3, 5] to [5, 2]
      count([fieldType[3, 5], fieldType[4, 4], fieldType[5, 4]], f) <= 1 /\
      % Row from [5,2] to [5,4]
      count([fieldType[5, 2], fieldType[5, 3], fieldType[5, 4]], f) <= 1
    ) /\
    % Row 1-2
    neighbourhoodAllotmentScore[ 1] = 4 * sum([weightedFieldAllotment[1, 2], weightedFieldAllotment[1, 3], weightedFieldAllotment[2, 2]]) /\
    neighbourhoodAllotmentScore[ 2] = 4 * sum([weightedFieldAllotment[1, 3], weightedFieldAllotment[1, 4], weightedFieldAllotment[2, 3]]) /\
    % Row 2-1
    neighbourhoodAllotmentScore[ 3] = 4 * sum([weightedFieldAllotment[1, 2], weightedFieldAllotment[2, 1], weightedFieldAllotment[2, 2]]) /\
    neighbourhoodAllotmentScore[ 4] = 4 * sum([weightedFieldAllotment[1, 3], weightedFieldAllotment[2, 2], weightedFieldAllotment[2, 3]]) /\
    neighbourhoodAllotmentScore[ 5] = 4 * sum([weightedFieldAllotment[1, 4], weightedFieldAllotment[2, 3], weightedFieldAllotment[2, 4]]) /\
    % row 2-3
    neighbourhoodAllotmentScore[ 6] = 4 * sum([weightedFieldAllotment[2, 1], weightedFieldAllotment[2, 2], weightedFieldAllotment[3, 2]]) /\
    neighbourhoodAllotmentScore[ 7] = 4 * sum([weightedFieldAllotment[2, 3], weightedFieldAllotment[2, 4], weightedFieldAllotment[3, 4]]) /\
    % row 3-2
    neighbourhoodAllotmentScore[ 8] = 4 * sum([weightedFieldAllotment[2, 1], weightedFieldAllotment[3, 1], weightedFieldAllotment[3, 2]]) /\
    neighbourhoodAllotmentScore[ 9] = 4 * sum([weightedFieldAllotment[2, 4], weightedFieldAllotment[3, 4], weightedFieldAllotment[3, 5]]) /\
    % row 3-4
    neighbourhoodAllotmentScore[10] = 4 * sum([weightedFieldAllotment[3, 1], weightedFieldAllotment[3, 2], weightedFieldAllotment[4, 1]]) /\
    neighbourhoodAllotmentScore[11] = 4 * sum([weightedFieldAllotment[3, 4], weightedFieldAllotment[3, 5], weightedFieldAllotment[4, 4]]) /\
    % row 4-3
    neighbourhoodAllotmentScore[12] = 4 * sum([weightedFieldAllotment[3, 2], weightedFieldAllotment[4, 1], weightedFieldAllotment[4, 2]]) /\
    neighbourhoodAllotmentScore[13] = 4 * sum([weightedFieldAllotment[3, 4], weightedFieldAllotment[4, 3], weightedFieldAllotment[4, 4]]) /\
    % row 4-5
    neighbourhoodAllotmentScore[14] = 4 * sum([weightedFieldAllotment[4, 1], weightedFieldAllotment[4, 2], weightedFieldAllotment[5, 2]]) /\
    neighbourhoodAllotmentScore[15] = 4 * sum([weightedFieldAllotment[4, 2], weightedFieldAllotment[4, 3], weightedFieldAllotment[5, 3]]) /\
    neighbourhoodAllotmentScore[16] = 4 * sum([weightedFieldAllotment[4, 3], weightedFieldAllotment[4, 4], weightedFieldAllotment[5, 4]]) /\
    % row 5-4
    neighbourhoodAllotmentScore[17] = 4 * sum([weightedFieldAllotment[4, 2], weightedFieldAllotment[5, 2], weightedFieldAllotment[5, 3]]) /\
    neighbourhoodAllotmentScore[18] = 4 * sum([weightedFieldAllotment[4, 3], weightedFieldAllotment[5, 3], weightedFieldAllotment[5, 4]]) /\
    %neighbourhoodAllotmentScore[row, col] = 4 * sum(dRow, dCol in {-1, 0, 1} where 
    %   row + dRow >  0 /\
    %   col + dCol >  0 /\
    %   row + dRow <= rowCount /\
    %   col + dCol <= colCount /\
    %   active[row + dRow, col + dCol] == 1 /\
    %   (dRow == 0 \/                       % Must be on the same row,
    %     ((row mod 2 == 1 /\ dCol <= 0) \/ % if currentl is on an odd row, then match must be on non-following column, or
    %      (row mod 2 == 0 /\ dCol >= 0))   % if currentl is on an even row, then match must be on non-previous column.
    %  % )
    %) (weightedFieldAllotment[row + dRow, col + dCol])
    %/\
    % Row 1-2
    % Different Field Types
    all_different([fieldType[1, 2], fieldType[1, 3], fieldType[2, 2]]) /\
    all_different([fieldType[1, 3], fieldType[1, 4], fieldType[2, 3]]) /\
    % Row 2-1
    all_different([fieldType[1, 2], fieldType[2, 1], fieldType[2, 2]]) /\
    all_different([fieldType[1, 3], fieldType[2, 2], fieldType[2, 3]]) /\
    all_different([fieldType[1, 4], fieldType[2, 3], fieldType[2, 4]]) /\
    % row 2-3
    all_different([fieldType[2, 1], fieldType[2, 2], fieldType[3, 2]]) /\
    %all_different([fieldType[2, 2], fieldType[2, 3], fieldType[3, 3]]) /\
    all_different([fieldType[2, 3], fieldType[2, 4], fieldType[3, 4]]) /\
    % row 3-2
    all_different([fieldType[2, 1], fieldType[3, 1], fieldType[3, 2]]) /\
    %all_different([fieldType[2, 2], fieldType[3, 2], fieldType[3, 3]]) /\
    %all_different([fieldType[2, 3], fieldType[3, 3], fieldType[3, 4]]) /\
    all_different([fieldType[2, 4], fieldType[3, 4], fieldType[3, 5]]) /\
    % row 3-4
    all_different([fieldType[3, 1], fieldType[3, 2], fieldType[4, 1]]) /\
    %all_different([fieldType[3, 2], fieldType[3, 3], fieldType[4, 2]]) /\
    %all_different([fieldType[3, 3], fieldType[3, 4], fieldType[4, 3]]) /\
    all_different([fieldType[3, 4], fieldType[3, 5], fieldType[4, 4]]) /\
    % row 4-3
    all_different([fieldType[3, 2], fieldType[4, 1], fieldType[4, 2]]) /\
    %all_different([fieldType[3, 3], fieldType[4, 2], fieldType[4, 3]]) /\
    all_different([fieldType[3, 4], fieldType[4, 3], fieldType[4, 4]]) /\
    % row 4-5
    all_different([fieldType[4, 1], fieldType[4, 2], fieldType[5, 2]]) /\
    all_different([fieldType[4, 2], fieldType[4, 3], fieldType[5, 3]]) /\
    all_different([fieldType[4, 3], fieldType[4, 4], fieldType[5, 4]]) /\
    % row 5-4
    all_different([fieldType[4, 2], fieldType[5, 3], fieldType[5, 4]]) /\
    all_different([fieldType[4, 3], fieldType[5, 3], fieldType[5, 4]]) /\
    % Different Numbers
    % Row 1-2
    all_different([fieldAllotment[1, 2], fieldAllotment[1, 3], fieldAllotment[2, 2]]) /\
    all_different([fieldAllotment[1, 3], fieldAllotment[1, 4], fieldAllotment[2, 3]]) /\
    % Row 2-1
    all_different([fieldAllotment[1, 2], fieldAllotment[2, 1], fieldAllotment[2, 2]]) /\
    all_different([fieldAllotment[1, 3], fieldAllotment[2, 2], fieldAllotment[2, 3]]) /\
    all_different([fieldAllotment[1, 4], fieldAllotment[2, 3], fieldAllotment[2, 4]]) /\
    % row 2-3
    all_different([fieldAllotment[2, 1], fieldAllotment[2, 2], fieldAllotment[3, 2]]) /\
    all_different([fieldAllotment[2, 2], fieldAllotment[2, 3], fieldAllotment[3, 3]]) /\
    all_different([fieldAllotment[2, 3], fieldAllotment[2, 4], fieldAllotment[3, 4]]) /\
    % row 3-2
    all_different([fieldAllotment[2, 1], fieldAllotment[3, 1], fieldAllotment[3, 2]]) /\
    all_different([fieldAllotment[2, 2], fieldAllotment[3, 2], fieldAllotment[3, 3]]) /\
    all_different([fieldAllotment[2, 3], fieldAllotment[3, 3], fieldAllotment[3, 4]]) /\
    all_different([fieldAllotment[2, 4], fieldAllotment[3, 4], fieldAllotment[3, 5]]) /\
    % row 3-4
    all_different([fieldAllotment[3, 1], fieldAllotment[3, 2], fieldAllotment[4, 1]]) /\
    all_different([fieldAllotment[3, 2], fieldAllotment[3, 3], fieldAllotment[4, 2]]) /\
    all_different([fieldAllotment[3, 3], fieldAllotment[3, 4], fieldAllotment[4, 3]]) /\
    all_different([fieldAllotment[3, 4], fieldAllotment[3, 5], fieldAllotment[4, 4]]) /\
    % row 4-3
    all_different([fieldAllotment[3, 2], fieldAllotment[4, 1], fieldAllotment[4, 2]]) /\
    all_different([fieldAllotment[3, 3], fieldAllotment[4, 2], fieldAllotment[4, 3]]) /\
    all_different([fieldAllotment[3, 4], fieldAllotment[4, 3], fieldAllotment[4, 4]]) /\
    % row 4-5
    all_different([fieldAllotment[4, 1], fieldAllotment[4, 2], fieldAllotment[5, 2]]) /\
    all_different([fieldAllotment[4, 2], fieldAllotment[4, 3], fieldAllotment[5, 3]]) /\
    all_different([fieldAllotment[4, 3], fieldAllotment[4, 4], fieldAllotment[5, 4]]) /\
    % row 5-4
    all_different([fieldAllotment[4, 2], fieldAllotment[5, 2], fieldAllotment[5, 3]]) /\
    all_different([fieldAllotment[4, 3], fieldAllotment[5, 3], fieldAllotment[5, 4]]) /\
    %forall(a in row..rowCount, b in 1..colCount where 
      %active[a, b] == 1 /\
      %(a > row \/ b > col)
    %) (
       %not (fieldType[row, col] == fieldType[a, b] /\ fieldAllotment[row, col] == fieldAllotment[a, b])
    %) /\
    forall(n in 1..length(allotments)) (
      count(array1d(fieldAllotment), allotments[n], allotmentsCount[n])
    )
    /\
    forall(f in 1..6) (
      count(array1d(fieldType), f, fieldTypesCount[f])
    )
    /\
    alldifferent_except_0(array1d(fieldTypeAllotment))
    /\
    forall(f in 1..5) (
      fieldTypeScore[f] = (12 / fieldTypesCount[f]) * sum(row in 1..rowCount, col in 1..colCount where 
        active[row, col] == 1 /\
        fieldType[row, col] == f
      ) (weightedFieldAllotment[row, col])
    )
;
solve minimize ((max(fieldTypeScore) - min(fieldTypeScore)) +
                (max(neighbourhoodAllotmentScore) - min(neighbourhoodAllotmentScore)));
%solve :: int_search([fieldType[i,j] | i in 1..r, j in 1..c], first_fail, indomain_min, complete) satisfy;


%  O O
%O O O
%O O

output 
[ "\nHexagons:" ] ++
[
  if col = 1 then 
    "\n" ++
    if row mod 2  == 0 then
      if line <= 2 /\ row > 1 /\ active[row - 1, col] == 1 then
        if line = 1 then
          "'. "
        else
          "  `"
        endif
      else
        "   "
      endif
    else
      ""
    endif
  else
    ""
  endif ++
%0,1,1,1,0,
%1,1,1,1,0,
%1,1,1,1,1,
%1,1,1,1,0,
%0,1,1,1,0
  if line = 1 then
    if active[row, col] == 1 then
      "  .'. "
    elseif (row mod 2 == 0 /\ row > 1 /\ col < colCount /\ active[row - 1, col + 1] == 1) \/ 
           (row mod 2 == 1 /\ row > 1 /\ active[row - 1, col] == 1) then
      "   '. "
    elseif (row mod 2 == 0 /\ row > 1 /\ active[row - 1, col] == 1) \/ 
           (row mod 2 == 1 /\ row > 1 /\ col > 1 /\ active[row - 1, col - 1] == 1) then
      "  .'  "
    else
      "      "
    endif
  elseif line = 2 then
    if active[row, col] == 1 then
      ".´" ++
      if string_length(show(fieldAllotment[row, col])) >= 3 then
        show(fieldAllotment[row, col]) 
      elseif string_length(show(fieldAllotment[row, col])) >= 2 then
        " " ++ show(fieldAllotment[row, col])
      else
        "  " ++ show(fieldAllotment[row, col])
      endif ++
      "`" ++
      if col = colCount \/ active[row, col + 1] == 0 then "." else "" endif
    elseif (row mod 2 == 0 /\ row > 1 /\ col < colCount /\ active[row - 1, col + 1] == 1) \/ 
           (row mod 2 == 1 /\ row > 1 /\ active[row - 1, col] == 1) then
      "     `"
    elseif (row mod 2 == 0 /\ row > 1 /\ active[row - 1, col] == 1) \/ 
           (row mod 2 == 1 /\ row > 1 /\ col > 1 /\ active[row - 1, col - 1] == 1) then
      ".´    "
    else
      "      "
    endif
  else
    if active[row, col] == 1 then
      "|N:" ++
      if string_length(show(fieldType[row, col])) >= 3 then
        show(fieldType[row, col])
      elseif string_length(show(fieldType[row, col])) >= 2 then
        " " ++ show(fieldType[row, col])
      else
        "  " ++ show(fieldType[row, col])
      endif ++
      if col = colCount then "|" else "" endif
    else
      if col > 1 /\ active[row, col - 1] == 1 then "|" else "" endif ++
      "      "
    endif
  endif
  | row in 1..rowCount, line in 1..3, col in 1..colCount
] ++
[
  if col = 1 then 
    "\n"
  else 
    ""
  endif ++
  if line = 1 then
    if active[rowCount, col] == 1 then
      "'.   ." ++
      if col = colCount \/ active[rowCount, col + 1] == 0 then "'" else "" endif
    else
      "      "
    endif
  else
    if active[rowCount, col] == 1 then
      "  `.´ " ++
      if col = colCount then "." else "" endif
    else
      "      "
    endif
  endif 
  | line in 1..2, col in 1..colCount
] ++ ["\n" ++ 
"\nNeighbourhood score: " ++ show(max([neighbourhoodAllotmentScore[i] | i in 1..18]) - 
                                  min([neighbourhoodAllotmentScore[i] | i in 1..18])) ++
"\nField score:         " ++ show(max(fieldTypeScore) - min(fieldTypeScore)) ++ 
"\nTotal score:         " ++ show((max([neighbourhoodAllotmentScore[i] | i in 1..18]) - 
                                   min([neighbourhoodAllotmentScore[i] | i in 1..18])) + 
                                  (max(fieldTypeScore) - min(fieldTypeScore)))
];