                                                                                                                                                                                                                                                                                                                                                   2   2   2   2   2   2   2   2   2   2    2
HashTable{AOTideal => ideal (y y  - y y  - y y , y y  - y y  - y y , y y y   - y y y   - y y  y   + y y  y  , y y y   - y y y   - y y  y   + y y  y  , y y y   - y y y   - y y  y   + y y  y  , y y y  - y y y   - y y y   + y y y  , y y y  - y y y   - y y y   + y y y  , y y y  - y y y  - y y y  + y y y , y y y  - y y y  - y y y  + y y y , y , y , y , y , y , y , y , y , y , y  , y  )}
                              1 3    1 5    3 5   1 2    1 4    2 4   8 9 10    8 9 11    8 10 11    9 10 11   4 5 10    4 5 11    4 10 11    5 10 11   2 3 10    2 3 11    2 10 11    3 10 11   6 7 9    6 7 11    6 9 11    7 9 11   6 7 8    6 7 10    6 8 10    7 8 10   4 5 8    4 5 9    4 8 9    5 8 9   2 3 8    2 3 9    2 8 9    3 8 9   1   2   3   4   5   6   7   8   9   10   11
                                2    2    2   2   2   2   2   2   2         2         2
          AOTinIdeal => ideal (y  , y  , y , y , y , y , y , y , y , y y , y , y y , y , y y y  , y y y  , y y y  , y y y , y y y , y y y , y y y , y y y )
                                11   10   9   8   7   6   5   4   3   1 3   2   1 2   1   8 9 10   4 5 10   2 3 10   6 7 9   6 7 8   4 5 8   2 3 8   2 3 4
          graph => {set {0, 3}, set {3, 5}, set {3, 6}, set {0, 5}, set {0, 6}, set {1, 4}, set {2, 4}, set {1, 5}, set {1, 6}, set {2, 5}, set {2, 6}}
                                  2       3       4       5      6
          hSeries => 1 + 11T + 53T  + 140T  + 210T  + 167T  + 54T
          hyperplanes => {a - d, d - f, d - g, a - f, a - g, b - e, c - e, b - f, b - g, c - f, c - g}
          numVariables => 11
          WLPfull => "The AOT algebra has WLP"
          WLPin => "A does not have WLP at A_4"


R = QQ[y_1..y_11]
AOTideal = ideal map(R^1,R^{{-2}, {-2}, {-3}, {-3}, {-3}, {-3}, {-3}, {-3}, {-3}, {-2}, {-2}, {-2}, {-2}, {-2}, {-2}, {-2}, {-2}, {-2}, {-2}, {-2}},{{y_1*y_3-y_1*y_5-y_3*y_5, y_1*y_2-y_1*y_4-y_2*y_4, y_8*y_9*y_10-y_8*y_9*y_11-y_8*y_10*y_11+y_9*y_10*y_11, y_4*y_5*y_10-y_4*y_5*y_11-y_4*y_10*y_11+y_5*y_10*y_11, y_2*y_3*y_10-y_2*y_3*y_11-y_2*y_10*y_11+y_3*y_10*y_11, y_6*y_7*y_9-y_6*y_7*y_11-y_6*y_9*y_11+y_7*y_9*y_11, y_6*y_7*y_8-y_6*y_7*y_10-y_6*y_8*y_10+y_7*y_8*y_10, y_4*y_5*y_8-y_4*y_5*y_9-y_4*y_8*y_9+y_5*y_8*y_9, y_2*y_3*y_8-y_2*y_3*y_9-y_2*y_8*y_9+y_3*y_8*y_9, y_1^2, y_2^2, y_3^2, y_4^2, y_5^2, y_6^2, y_7^2, y_8^2, y_9^2, y_10^2, y_11^2}})
AOTinIdeal = ideal map(R^1,R^{{-2}, {-2}, {-2}, {-2}, {-2}, {-2}, {-2}, {-2}, {-2}, {-2}, {-2}, {-2}, {-2}, {-3}, {-3}, {-3}, {-3}, {-3}, {-3}, {-3}, {-3}},{{y_11^2, y_10^2, y_9^2, y_8^2, y_7^2, y_6^2, y_5^2, y_4^2, y_3^2, y_1*y_3, y_2^2, y_1*y_2, y_1^2, y_8*y_9*y_10, y_4*y_5*y_10, y_2*y_3*y_10, y_6*y_7*y_9, y_6*y_7*y_8, y_4*y_5*y_8, y_2*y_3*y_8, y_2*y_3*y_4}})
G = graph {set {0, 3}, set {3, 5}, set {3, 6}, set {0, 5}, set {0, 6}, set {1, 4}, set {2, 4}, set {1, 5}, set {1, 6}, set {2, 5}, set {2, 6}}
