                                                                                                                                                                                                                                                              2   2   2   2   2   2   2   2   2   2    2    2
HashTable{AOTideal => ideal (y y   - y y   + y  y  , y y  - y y   - y y  , y y  - y y   - y y  , y y  - y y   + y y  , y y  - y y  - y y , y y y   - y y y   - y y  y   + y y  y  , y y y  - y y y   - y y y   + y y y  , y y y  - y y y  - y y y  + y y y , y , y , y , y , y , y , y , y , y , y  , y  , y  )}
                              9 11    9 12    11 12   6 8    6 11    8 11   6 7    6 10    7 10   3 5    3 12    5 12   1 2    1 3    2 3   4 5 10    4 5 11    4 10 11    5 10 11   3 4 9    3 4 10    3 9 10    4 9 10   4 5 7    4 5 8    4 7 8    5 7 8   1   2   3   4   5   6   7   8   9   10   11   12
                                2    2           2    2   2         2         2   2         2   2   2         2
          AOTinIdeal => ideal (y  , y  , y y  , y  , y , y , y y , y , y y , y , y , y y , y , y , y , y y , y , y y y  , y y y  , y y y , y y y , y y y  y  , y y y y )
                                12   11   9 11   10   9   8   6 8   7   6 7   6   5   3 5   4   3   2   1 2   1   7 8 10   4 5 10   3 4 9   4 5 7   3 4 10 11   3 4 7 8
          graph => {set {0, 2}, set {2, 4}, set {0, 4}, set {0, 5}, set {0, 6}, set {1, 3}, set {3, 5}, set {3, 6}, set {1, 4}, set {1, 5}, set {1, 6}, set {4, 6}}
                                  2       3       4       5      6
          hSeries => 1 + 12T + 61T  + 167T  + 257T  + 208T  + 68T
          hyperplanes => {a - c, c - e, a - e, a - f, a - g, b - d, d - f, d - g, b - e, b - f, b - g, e - g}
          numVariables => 12
          WLPfull => "The AOT algebra has WLP"
          WLPin => "A does not have WLP at A_4"


R = QQ[y_1..y_12]
AOTideal = ideal map(R^1,R^{{-2}, {-2}, {-2}, {-2}, {-2}, {-3}, {-3}, {-3}, {-2}, {-2}, {-2}, {-2}, {-2}, {-2}, {-2}, {-2}, {-2}, {-2}, {-2}, {-2}},{{y_9*y_11-y_9*y_12+y_11*y_12, y_6*y_8-y_6*y_11-y_8*y_11, y_6*y_7-y_6*y_10-y_7*y_10, y_3*y_5-y_3*y_12+y_5*y_12, y_1*y_2-y_1*y_3-y_2*y_3, y_4*y_5*y_10-y_4*y_5*y_11-y_4*y_10*y_11+y_5*y_10*y_11, y_3*y_4*y_9-y_3*y_4*y_10-y_3*y_9*y_10+y_4*y_9*y_10, y_4*y_5*y_7-y_4*y_5*y_8-y_4*y_7*y_8+y_5*y_7*y_8, y_1^2, y_2^2, y_3^2, y_4^2, y_5^2, y_6^2, y_7^2, y_8^2, y_9^2, y_10^2, y_11^2, y_12^2}})
AOTinIdeal = ideal map(R^1,R^{{-2}, {-2}, {-2}, {-2}, {-2}, {-2}, {-2}, {-2}, {-2}, {-2}, {-2}, {-2}, {-2}, {-2}, {-2}, {-2}, {-2}, {-3}, {-3}, {-3}, {-3}, {-4}, {-4}},{{y_12^2, y_11^2, y_9*y_11, y_10^2, y_9^2, y_8^2, y_6*y_8, y_7^2, y_6*y_7, y_6^2, y_5^2, y_3*y_5, y_4^2, y_3^2, y_2^2, y_1*y_2, y_1^2, y_7*y_8*y_10, y_4*y_5*y_10, y_3*y_4*y_9, y_4*y_5*y_7, y_3*y_4*y_10*y_11, y_3*y_4*y_7*y_8}})
G = graph {set {0, 2}, set {2, 4}, set {0, 4}, set {0, 5}, set {0, 6}, set {1, 3}, set {3, 5}, set {3, 6}, set {1, 4}, set {1, 5}, set {1, 6}, set {4, 6}}
