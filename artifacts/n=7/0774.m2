                                                                                                                                                                                                                                                                                                 2   2   2   2   2   2   2   2   2   2    2    2    2
HashTable{AOTideal => ideal (y  y   - y  y   - y  y  , y y  - y y   + y y  , y y  - y y   + y y  , y y  - y y   + y y  , y y  - y y   + y y  , y y  - y y  - y y , y y  - y y  - y y , y y y  - y y y  - y y y  + y y y , y y y  - y y y  - y y y  + y y y , y y y  - y y y  - y y y  + y y y , y , y , y , y , y , y , y , y , y , y  , y  , y  , y  )}
                              11 12    11 13    12 13   8 9    8 12    9 12   7 9    7 10    9 10   5 6    5 12    6 12   4 6    4 10    6 10   2 3    2 8    3 8   1 3    1 5    3 5   4 5 7    4 5 8    4 7 8    5 7 8   1 2 6    1 2 9    1 6 9    2 6 9   1 2 4    1 2 7    1 4 7    2 4 7   1   2   3   4   5   6   7   8   9   10   11   12   13
                                2    2            2    2    2               2   2   2               2   2   2               2   2
          AOTinIdeal => ideal (y  , y  , y  y  , y  , y  , y , y y , y y , y , y , y , y y , y y , y , y , y , y y , y y , y , y , y y y  , y y y  , y y y , y y y , y y y , y y y )
                                13   12   11 12   11   10   9   8 9   7 9   8   7   6   5 6   4 6   5   4   3   2 3   1 3   2   1   7 8 10   4 5 10   4 5 7   1 2 6   1 2 5   1 2 4
          graph => {set {0, 3}, set {1, 3}, set {3, 5}, set {0, 4}, set {0, 5}, set {0, 6}, set {1, 4}, set {1, 5}, set {1, 6}, set {4, 6}, set {2, 5}, set {5, 6}, set {2, 6}}
                                  2       3       4       5      6
          hSeries => 1 + 13T + 71T  + 206T  + 331T  + 276T  + 92T
          hyperplanes => {a - d, b - d, d - f, a - e, a - f, a - g, b - e, b - f, b - g, e - g, c - f, f - g, c - g}
          numVariables => 13
          WLPfull => "The AOT algebra has WLP"
          WLPin => "A does not have WLP at A_4"


R = QQ[y_1..y_13]
AOTideal = ideal map(R^1,R^{{-2}, {-2}, {-2}, {-2}, {-2}, {-2}, {-2}, {-3}, {-3}, {-3}, {-2}, {-2}, {-2}, {-2}, {-2}, {-2}, {-2}, {-2}, {-2}, {-2}, {-2}, {-2}, {-2}},{{y_11*y_12-y_11*y_13-y_12*y_13, y_8*y_9-y_8*y_12+y_9*y_12, y_7*y_9-y_7*y_10+y_9*y_10, y_5*y_6-y_5*y_12+y_6*y_12, y_4*y_6-y_4*y_10+y_6*y_10, y_2*y_3-y_2*y_8-y_3*y_8, y_1*y_3-y_1*y_5-y_3*y_5, y_4*y_5*y_7-y_4*y_5*y_8-y_4*y_7*y_8+y_5*y_7*y_8, y_1*y_2*y_6-y_1*y_2*y_9-y_1*y_6*y_9+y_2*y_6*y_9, y_1*y_2*y_4-y_1*y_2*y_7-y_1*y_4*y_7+y_2*y_4*y_7, y_1^2, y_2^2, y_3^2, y_4^2, y_5^2, y_6^2, y_7^2, y_8^2, y_9^2, y_10^2, y_11^2, y_12^2, y_13^2}})
AOTinIdeal = ideal map(R^1,R^{{-2}, {-2}, {-2}, {-2}, {-2}, {-2}, {-2}, {-2}, {-2}, {-2}, {-2}, {-2}, {-2}, {-2}, {-2}, {-2}, {-2}, {-2}, {-2}, {-2}, {-3}, {-3}, {-3}, {-3}, {-3}, {-3}},{{y_13^2, y_12^2, y_11*y_12, y_11^2, y_10^2, y_9^2, y_8*y_9, y_7*y_9, y_8^2, y_7^2, y_6^2, y_5*y_6, y_4*y_6, y_5^2, y_4^2, y_3^2, y_2*y_3, y_1*y_3, y_2^2, y_1^2, y_7*y_8*y_10, y_4*y_5*y_10, y_4*y_5*y_7, y_1*y_2*y_6, y_1*y_2*y_5, y_1*y_2*y_4}})
G = graph {set {0, 3}, set {1, 3}, set {3, 5}, set {0, 4}, set {0, 5}, set {0, 6}, set {1, 4}, set {1, 5}, set {1, 6}, set {4, 6}, set {2, 5}, set {5, 6}, set {2, 6}}
