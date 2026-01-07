                                                                                                                                                                                                                                                                                                                         2   2   2   2   2   2   2   2   2   2    2    2
HashTable{AOTideal => ideal (y y  - y y   - y y  , y y  - y y   - y y  , y y  - y y  - y y , y y  - y y  - y y , y y y   - y y y   - y y  y   + y y  y  , y y y   - y y y   - y y  y   + y y  y  , y y y   - y y y   - y y  y   + y y  y  , y y y   - y y y   - y y  y   + y y  y  , y y y  - y y y  - y y y  + y y y , y , y , y , y , y , y , y , y , y , y  , y  , y  )}
                              7 9    7 12    9 12   7 8    7 11    8 11   1 3    1 6    3 6   1 2    1 4    2 4   5 6 11    5 6 12    5 11 12    6 11 12   4 6 10    4 6 12    4 10 12    6 10 12   4 5 10    4 5 11    4 10 11    5 10 11   2 3 10    2 3 12    2 10 12    3 10 12   5 6 8    5 6 9    5 8 9    6 8 9   1   2   3   4   5   6   7   8   9   10   11   12
                                2    2    2    2         2         2   2   2   2   2         2         2
          AOTinIdeal => ideal (y  , y  , y  , y , y y , y , y y , y , y , y , y , y , y y , y , y y , y , y y y  , y y y  , y y y  , y y y  , y y y  , y y y , y y y )
                                12   11   10   9   7 9   8   7 8   7   6   5   4   3   1 3   2   1 2   1   8 9 11   5 6 11   4 6 10   4 5 10   2 3 10   5 6 8   2 3 4
          graph => {set {0, 2}, set {2, 4}, set {2, 6}, set {0, 4}, set {0, 5}, set {0, 6}, set {1, 3}, set {3, 5}, set {3, 6}, set {1, 4}, set {1, 5}, set {1, 6}}
                                  2       3       4       5      6
          hSeries => 1 + 12T + 62T  + 175T  + 281T  + 239T  + 82T
          hyperplanes => {a - c, c - e, c - g, a - e, a - f, a - g, b - d, d - f, d - g, b - e, b - f, b - g}
          numVariables => 12
          WLPfull => "The AOT algebra has WLP"
          WLPin => "A does not have WLP at A_4"


R = QQ[y_1..y_12]
AOTideal = ideal map(R^1,R^{{-2}, {-2}, {-2}, {-2}, {-3}, {-3}, {-3}, {-3}, {-3}, {-2}, {-2}, {-2}, {-2}, {-2}, {-2}, {-2}, {-2}, {-2}, {-2}, {-2}, {-2}},{{y_7*y_9-y_7*y_12-y_9*y_12, y_7*y_8-y_7*y_11-y_8*y_11, y_1*y_3-y_1*y_6-y_3*y_6, y_1*y_2-y_1*y_4-y_2*y_4, y_5*y_6*y_11-y_5*y_6*y_12-y_5*y_11*y_12+y_6*y_11*y_12, y_4*y_6*y_10-y_4*y_6*y_12-y_4*y_10*y_12+y_6*y_10*y_12, y_4*y_5*y_10-y_4*y_5*y_11-y_4*y_10*y_11+y_5*y_10*y_11, y_2*y_3*y_10-y_2*y_3*y_12-y_2*y_10*y_12+y_3*y_10*y_12, y_5*y_6*y_8-y_5*y_6*y_9-y_5*y_8*y_9+y_6*y_8*y_9, y_1^2, y_2^2, y_3^2, y_4^2, y_5^2, y_6^2, y_7^2, y_8^2, y_9^2, y_10^2, y_11^2, y_12^2}})
AOTinIdeal = ideal map(R^1,R^{{-2}, {-2}, {-2}, {-2}, {-2}, {-2}, {-2}, {-2}, {-2}, {-2}, {-2}, {-2}, {-2}, {-2}, {-2}, {-2}, {-3}, {-3}, {-3}, {-3}, {-3}, {-3}, {-3}},{{y_12^2, y_11^2, y_10^2, y_9^2, y_7*y_9, y_8^2, y_7*y_8, y_7^2, y_6^2, y_5^2, y_4^2, y_3^2, y_1*y_3, y_2^2, y_1*y_2, y_1^2, y_8*y_9*y_11, y_5*y_6*y_11, y_4*y_6*y_10, y_4*y_5*y_10, y_2*y_3*y_10, y_5*y_6*y_8, y_2*y_3*y_4}})
G = graph {set {0, 2}, set {2, 4}, set {2, 6}, set {0, 4}, set {0, 5}, set {0, 6}, set {1, 3}, set {3, 5}, set {3, 6}, set {1, 4}, set {1, 5}, set {1, 6}}
