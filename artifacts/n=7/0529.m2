                                                                                                                                                                                                                                                                                                                                                             2   2   2   2   2   2   2   2   2   2    2    2
HashTable{AOTideal => ideal (y y  - y y   - y y  , y y  - y y  + y y , y y  - y y  - y y , y y  - y y  - y y , y y  y   - y y  y   - y y  y   + y  y  y  , y y y   - y y y   - y y  y   + y y  y  , y y y   - y y y   - y y  y   + y y  y  , y y y  - y y y   - y y y   + y y y  , y y y  - y y y   - y y y   + y y y  , y y y  - y y y  - y y y  + y y y , y , y , y , y , y , y , y , y , y , y  , y  , y  )}
                              7 8    7 10    8 10   4 6    4 8    6 8   1 3    1 6    3 6   1 2    1 5    2 5   9 10 11    9 10 12    9 11 12    10 11 12   5 6 11    5 6 12    5 11 12    6 11 12   2 3 11    2 3 12    2 11 12    3 11 12   5 6 9    5 6 10    5 9 10    6 9 10   2 3 9    2 3 10    2 9 10    3 9 10   4 5 7    4 5 9    4 7 9    5 7 9   1   2   3   4   5   6   7   8   9   10   11   12
                                2    2    2    2   2         2   2         2   2   2         2         2
          AOTinIdeal => ideal (y  , y  , y  , y , y , y y , y , y , y y , y , y , y , y y , y , y y , y , y y  y  , y y y  , y y y  , y y y , y y y , y y y , y y y , y y y y  , y y y y )
                                12   11   10   9   8   7 8   7   6   4 6   5   4   3   1 3   2   1 2   1   9 10 11   5 6 11   2 3 11   5 6 9   2 3 9   4 5 7   2 3 5   4 5 8 11   4 5 8 9
          graph => {set {0, 3}, set {3, 5}, set {3, 6}, set {0, 4}, set {0, 5}, set {0, 6}, set {1, 4}, set {4, 6}, set {1, 5}, set {1, 6}, set {2, 5}, set {2, 6}}
                                  2       3       4       5      6
          hSeries => 1 + 12T + 62T  + 174T  + 275T  + 228T  + 76T
          hyperplanes => {a - d, d - f, d - g, a - e, a - f, a - g, b - e, e - g, b - f, b - g, c - f, c - g}
          numVariables => 12
          WLPfull => "The AOT algebra has WLP"
          WLPin => "A does not have WLP at A_4"


R = QQ[y_1..y_12]
AOTideal = ideal map(R^1,R^{{-2}, {-2}, {-2}, {-2}, {-3}, {-3}, {-3}, {-3}, {-3}, {-3}, {-2}, {-2}, {-2}, {-2}, {-2}, {-2}, {-2}, {-2}, {-2}, {-2}, {-2}, {-2}},{{y_7*y_8-y_7*y_10-y_8*y_10, y_4*y_6-y_4*y_8+y_6*y_8, y_1*y_3-y_1*y_6-y_3*y_6, y_1*y_2-y_1*y_5-y_2*y_5, y_9*y_10*y_11-y_9*y_10*y_12-y_9*y_11*y_12+y_10*y_11*y_12, y_5*y_6*y_11-y_5*y_6*y_12-y_5*y_11*y_12+y_6*y_11*y_12, y_2*y_3*y_11-y_2*y_3*y_12-y_2*y_11*y_12+y_3*y_11*y_12, y_5*y_6*y_9-y_5*y_6*y_10-y_5*y_9*y_10+y_6*y_9*y_10, y_2*y_3*y_9-y_2*y_3*y_10-y_2*y_9*y_10+y_3*y_9*y_10, y_4*y_5*y_7-y_4*y_5*y_9-y_4*y_7*y_9+y_5*y_7*y_9, y_1^2, y_2^2, y_3^2, y_4^2, y_5^2, y_6^2, y_7^2, y_8^2, y_9^2, y_10^2, y_11^2, y_12^2}})
AOTinIdeal = ideal map(R^1,R^{{-2}, {-2}, {-2}, {-2}, {-2}, {-2}, {-2}, {-2}, {-2}, {-2}, {-2}, {-2}, {-2}, {-2}, {-2}, {-2}, {-3}, {-3}, {-3}, {-3}, {-3}, {-3}, {-3}, {-4}, {-4}},{{y_12^2, y_11^2, y_10^2, y_9^2, y_8^2, y_7*y_8, y_7^2, y_6^2, y_4*y_6, y_5^2, y_4^2, y_3^2, y_1*y_3, y_2^2, y_1*y_2, y_1^2, y_9*y_10*y_11, y_5*y_6*y_11, y_2*y_3*y_11, y_5*y_6*y_9, y_2*y_3*y_9, y_4*y_5*y_7, y_2*y_3*y_5, y_4*y_5*y_8*y_11, y_4*y_5*y_8*y_9}})
G = graph {set {0, 3}, set {3, 5}, set {3, 6}, set {0, 4}, set {0, 5}, set {0, 6}, set {1, 4}, set {4, 6}, set {1, 5}, set {1, 6}, set {2, 5}, set {2, 6}}
