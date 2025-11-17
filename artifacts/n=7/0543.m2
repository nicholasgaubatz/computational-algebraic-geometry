                                                                                                                                                                                                                                                      2   2   2   2   2   2   2   2   2   2    2    2    2
HashTable{AOTideal => ideal (y  y   - y  y   + y  y  , y y  - y y   + y y  , y y  - y y   - y y  , y y  - y y   - y y  , y y  - y y   + y y  , y y  - y y  + y y , y y  - y y  + y y , y y  - y y   + y y  , y y  - y y  - y y , y y  - y y  - y y , y , y , y , y , y , y , y , y , y , y  , y  , y  , y  )}
                              10 11    10 12    11 12   8 9    8 12    9 12   7 9    7 11    9 11   7 8    7 10    8 10   5 6    5 12    6 12   4 6    4 9    6 9   4 5    4 8    5 8   2 3    2 12    3 12   1 3    1 6    3 6   1 2    1 5    2 5   1   2   3   4   5   6   7   8   9   10   11   12   13
                                2    2    2            2    2               2         2   2               2         2   2               2         2
          AOTinIdeal => ideal (y  , y  , y  , y  y  , y  , y , y y , y y , y , y y , y , y , y y , y y , y , y y , y , y , y y , y y , y , y y , y )
                                13   12   11   10 11   10   9   8 9   7 9   8   7 8   7   6   5 6   4 6   5   4 5   4   3   2 3   1 3   2   1 2   1
          graph => {set {0, 3}, set {3, 5}, set {3, 6}, set {0, 4}, set {0, 5}, set {0, 6}, set {1, 4}, set {4, 5}, set {4, 6}, set {1, 5}, set {1, 6}, set {5, 6}, set {2, 6}}
                                  2       3       4       5      6
          hSeries => 1 + 13T + 68T  + 182T  + 261T  + 189T  + 54T
          hyperplanes => {a - d, d - f, d - g, a - e, a - f, a - g, b - e, e - f, e - g, b - f, b - g, f - g, c - g}
          numVariables => 13
          WLPfull => "The AOT algebra has WLP"
          WLPin => "A does not have WLP at A_3"


R = QQ[y_1..y_13]
AOTideal = ideal map(R^1,R^{{-2}, {-2}, {-2}, {-2}, {-2}, {-2}, {-2}, {-2}, {-2}, {-2}, {-2}, {-2}, {-2}, {-2}, {-2}, {-2}, {-2}, {-2}, {-2}, {-2}, {-2}, {-2}, {-2}},{{y_10*y_11-y_10*y_12+y_11*y_12, y_8*y_9-y_8*y_12+y_9*y_12, y_7*y_9-y_7*y_11-y_9*y_11, y_7*y_8-y_7*y_10-y_8*y_10, y_5*y_6-y_5*y_12+y_6*y_12, y_4*y_6-y_4*y_9+y_6*y_9, y_4*y_5-y_4*y_8+y_5*y_8, y_2*y_3-y_2*y_12+y_3*y_12, y_1*y_3-y_1*y_6-y_3*y_6, y_1*y_2-y_1*y_5-y_2*y_5, y_1^2, y_2^2, y_3^2, y_4^2, y_5^2, y_6^2, y_7^2, y_8^2, y_9^2, y_10^2, y_11^2, y_12^2, y_13^2}})
AOTinIdeal = ideal map(R^1,R^{{-2}, {-2}, {-2}, {-2}, {-2}, {-2}, {-2}, {-2}, {-2}, {-2}, {-2}, {-2}, {-2}, {-2}, {-2}, {-2}, {-2}, {-2}, {-2}, {-2}, {-2}, {-2}, {-2}},{{y_13^2, y_12^2, y_11^2, y_10*y_11, y_10^2, y_9^2, y_8*y_9, y_7*y_9, y_8^2, y_7*y_8, y_7^2, y_6^2, y_5*y_6, y_4*y_6, y_5^2, y_4*y_5, y_4^2, y_3^2, y_2*y_3, y_1*y_3, y_2^2, y_1*y_2, y_1^2}})
G = graph {set {0, 3}, set {3, 5}, set {3, 6}, set {0, 4}, set {0, 5}, set {0, 6}, set {1, 4}, set {4, 5}, set {4, 6}, set {1, 5}, set {1, 6}, set {5, 6}, set {2, 6}}
