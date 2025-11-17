                                                                                                                                                                                                                                                                                                                                                              2   2   2   2   2   2   2   2   2   2    2    2    2
HashTable{AOTideal => ideal (y  y   - y  y   + y  y  , y y   - y y   + y  y  , y y  - y y   - y y  , y y  - y y   - y y  , y y  - y y   + y y  , y y  - y y  - y y , y y y  - y y y   - y y y   + y y y  , y y y  - y y y   + y y y   - y y y  , y y y  - y y y   - y y y   + y y y  , y y y  - y y y  - y y y  + y y y , y y y  + y y y  - y y y  - y y y , y , y , y , y , y , y , y , y , y , y  , y  , y  , y  )}
                              11 12    11 13    12 13   9 10    9 13    10 13   7 8    7 12    8 12   6 8    6 10    8 10   2 3    2 13    3 13   1 2    1 5    2 5   6 7 9    6 7 11    6 9 11    7 9 11   4 5 8    4 5 13    4 8 13    5 8 13   4 5 7    4 5 11    4 7 11    5 7 11   4 5 6    4 5 9    4 6 9    5 6 9   1 3 4    1 3 8    1 4 8    3 4 8   1   2   3   4   5   6   7   8   9   10   11   12   13
                                2    2            2    2           2   2               2   2   2   2   2         2         2
          AOTinIdeal => ideal (y  , y  , y  y  , y  , y  , y y  , y , y , y y , y y , y , y , y , y , y , y y , y , y y , y , y y y  , y y y , y y y , y y y , y y y , y y y , y y y )
                                13   12   11 12   11   10   9 10   9   8   7 8   6 8   7   6   5   4   3   2 3   2   1 2   1   6 7 10   6 7 9   4 5 8   4 5 7   4 5 6   1 3 5   1 3 4
          graph => {set {0, 3}, set {3, 5}, set {3, 6}, set {0, 4}, set {0, 5}, set {1, 4}, set {2, 4}, set {4, 6}, set {1, 5}, set {1, 6}, set {2, 5}, set {2, 6}, set {5, 6}}
                                  2       3       4       5       6
          hSeries => 1 + 13T + 72T  + 215T  + 360T  + 315T  + 110T
          hyperplanes => {a - d, d - f, d - g, a - e, a - f, b - e, c - e, e - g, b - f, b - g, c - f, c - g, f - g}
          numVariables => 13
          WLPfull => "The AOT algebra has WLP"
          WLPin => "A does not have WLP at A_4"


R = QQ[y_1..y_13]
AOTideal = ideal map(R^1,R^{{-2}, {-2}, {-2}, {-2}, {-2}, {-2}, {-3}, {-3}, {-3}, {-3}, {-3}, {-2}, {-2}, {-2}, {-2}, {-2}, {-2}, {-2}, {-2}, {-2}, {-2}, {-2}, {-2}, {-2}},{{y_11*y_12-y_11*y_13+y_12*y_13, y_9*y_10-y_9*y_13+y_10*y_13, y_7*y_8-y_7*y_12-y_8*y_12, y_6*y_8-y_6*y_10-y_8*y_10, y_2*y_3-y_2*y_13+y_3*y_13, y_1*y_2-y_1*y_5-y_2*y_5, y_6*y_7*y_9-y_6*y_7*y_11-y_6*y_9*y_11+y_7*y_9*y_11, y_4*y_5*y_8-y_4*y_5*y_13+y_4*y_8*y_13-y_5*y_8*y_13, y_4*y_5*y_7-y_4*y_5*y_11-y_4*y_7*y_11+y_5*y_7*y_11, y_4*y_5*y_6-y_4*y_5*y_9-y_4*y_6*y_9+y_5*y_6*y_9, y_1*y_3*y_4+y_1*y_3*y_8-y_1*y_4*y_8-y_3*y_4*y_8, y_1^2, y_2^2, y_3^2, y_4^2, y_5^2, y_6^2, y_7^2, y_8^2, y_9^2, y_10^2, y_11^2, y_12^2, y_13^2}})
AOTinIdeal = ideal map(R^1,R^{{-2}, {-2}, {-2}, {-2}, {-2}, {-2}, {-2}, {-2}, {-2}, {-2}, {-2}, {-2}, {-2}, {-2}, {-2}, {-2}, {-2}, {-2}, {-2}, {-3}, {-3}, {-3}, {-3}, {-3}, {-3}, {-3}},{{y_13^2, y_12^2, y_11*y_12, y_11^2, y_10^2, y_9*y_10, y_9^2, y_8^2, y_7*y_8, y_6*y_8, y_7^2, y_6^2, y_5^2, y_4^2, y_3^2, y_2*y_3, y_2^2, y_1*y_2, y_1^2, y_6*y_7*y_10, y_6*y_7*y_9, y_4*y_5*y_8, y_4*y_5*y_7, y_4*y_5*y_6, y_1*y_3*y_5, y_1*y_3*y_4}})
G = graph {set {0, 3}, set {3, 5}, set {3, 6}, set {0, 4}, set {0, 5}, set {1, 4}, set {2, 4}, set {4, 6}, set {1, 5}, set {1, 6}, set {2, 5}, set {2, 6}, set {5, 6}}
