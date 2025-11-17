                                                                                                                                                                                    2   2   2   2   2   2   2   2   2   2    2    2
HashTable{AOTideal => ideal (y  y   - y  y   - y  y  , y y  - y y   + y y  , y y  - y y  - y y , y y  - y y   + y y  , y y  - y y  + y y , y y  - y y  + y y , y y  - y y  - y y , y , y , y , y , y , y , y , y , y , y  , y  , y  )}
                              10 11    10 12    11 12   7 8    7 11    8 11   6 8    6 9    8 9   4 5    4 11    5 11   3 5    3 8    5 8   3 4    3 7    4 7   1 2    1 5    2 5   1   2   3   4   5   6   7   8   9   10   11   12
                                2    2            2    2   2               2   2   2               2         2   2         2
          AOTinIdeal => ideal (y  , y  , y  y  , y  , y , y , y y , y y , y , y , y , y y , y y , y , y y , y , y , y y , y , y y y )
                                12   11   10 11   10   9   8   7 8   6 8   7   6   5   4 5   3 5   4   3 4   3   2   1 2   1   6 7 9
          graph => {set {0, 3}, set {3, 6}, set {0, 4}, set {0, 5}, set {0, 6}, set {1, 4}, set {4, 5}, set {4, 6}, set {1, 6}, set {2, 5}, set {5, 6}, set {2, 6}}
                                  2       3       4       5      6
          hSeries => 1 + 12T + 59T  + 152T  + 216T  + 160T  + 48T
          hyperplanes => {a - d, d - g, a - e, a - f, a - g, b - e, e - f, e - g, b - g, c - f, f - g, c - g}
          numVariables => 12
          WLPfull => "The AOT algebra has WLP"
          WLPin => "A does not have WLP at A_3"


R = QQ[y_1..y_12]
AOTideal = ideal map(R^1,R^{{-2}, {-2}, {-2}, {-2}, {-2}, {-2}, {-2}, {-2}, {-2}, {-2}, {-2}, {-2}, {-2}, {-2}, {-2}, {-2}, {-2}, {-2}, {-2}},{{y_10*y_11-y_10*y_12-y_11*y_12, y_7*y_8-y_7*y_11+y_8*y_11, y_6*y_8-y_6*y_9-y_8*y_9, y_4*y_5-y_4*y_11+y_5*y_11, y_3*y_5-y_3*y_8+y_5*y_8, y_3*y_4-y_3*y_7+y_4*y_7, y_1*y_2-y_1*y_5-y_2*y_5, y_1^2, y_2^2, y_3^2, y_4^2, y_5^2, y_6^2, y_7^2, y_8^2, y_9^2, y_10^2, y_11^2, y_12^2}})
AOTinIdeal = ideal map(R^1,R^{{-2}, {-2}, {-2}, {-2}, {-2}, {-2}, {-2}, {-2}, {-2}, {-2}, {-2}, {-2}, {-2}, {-2}, {-2}, {-2}, {-2}, {-2}, {-2}, {-3}},{{y_12^2, y_11^2, y_10*y_11, y_10^2, y_9^2, y_8^2, y_7*y_8, y_6*y_8, y_7^2, y_6^2, y_5^2, y_4*y_5, y_3*y_5, y_4^2, y_3*y_4, y_3^2, y_2^2, y_1*y_2, y_1^2, y_6*y_7*y_9}})
G = graph {set {0, 3}, set {3, 6}, set {0, 4}, set {0, 5}, set {0, 6}, set {1, 4}, set {4, 5}, set {4, 6}, set {1, 6}, set {2, 5}, set {5, 6}, set {2, 6}}
