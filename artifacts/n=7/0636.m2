                                                                                                                                                                                                                                                                                                      2   2   2   2   2   2   2   2   2   2    2    2
HashTable{AOTideal => ideal (y y  - y y   - y y  , y y  - y y   - y y  , y y  - y y   - y y  , y y  - y y  - y y , y y  - y y  - y y , y y  y   - y y  y   - y y  y   + y  y  y  , y y y   - y y y   - y y  y   + y y  y  , y y y  - y y y   - y y y   + y y y  , y y y  - y y y  - y y y  + y y y , y , y , y , y , y , y , y , y , y , y  , y  , y  )}
                              6 8    6 12    8 12   5 8    5 10    8 10   6 7    6 11    7 11   5 7    5 9    7 9   1 2    1 4    2 4   9 10 11    9 10 12    9 11 12    10 11 12   3 4 11    3 4 12    3 11 12    4 11 12   3 4 9    3 4 10    3 9 10    4 9 10   3 4 7    3 4 8    3 7 8    4 7 8   1   2   3   4   5   6   7   8   9   10   11   12
                                2    2    2    2   2               2               2   2   2   2   2         2
          AOTinIdeal => ideal (y  , y  , y  , y , y , y y , y y , y , y y , y y , y , y , y , y , y , y y , y , y y  y  , y y y  , y y y  , y y y  , y y y , y y y , y y y , y y y )
                                12   11   10   9   8   6 8   5 8   7   6 7   5 7   6   5   4   3   2   1 2   1   9 10 11   7 8 11   3 4 11   5 6 10   7 8 9   5 6 9   3 4 9   3 4 7
          graph => {set {0, 3}, set {3, 6}, set {0, 5}, set {0, 6}, set {1, 4}, set {2, 4}, set {4, 5}, set {4, 6}, set {1, 5}, set {1, 6}, set {2, 5}, set {2, 6}}
                                  2       3       4       5      6
          hSeries => 1 + 12T + 61T  + 166T  + 252T  + 200T  + 64T
          hyperplanes => {a - d, d - g, a - f, a - g, b - e, c - e, e - f, e - g, b - f, b - g, c - f, c - g}
          numVariables => 12
          WLPfull => "The AOT algebra has WLP"
          WLPin => "A does not have WLP at A_4"


R = QQ[y_1..y_12]
AOTideal = ideal map(R^1,R^{{-2}, {-2}, {-2}, {-2}, {-2}, {-3}, {-3}, {-3}, {-3}, {-2}, {-2}, {-2}, {-2}, {-2}, {-2}, {-2}, {-2}, {-2}, {-2}, {-2}, {-2}},{{y_6*y_8-y_6*y_12-y_8*y_12, y_5*y_8-y_5*y_10-y_8*y_10, y_6*y_7-y_6*y_11-y_7*y_11, y_5*y_7-y_5*y_9-y_7*y_9, y_1*y_2-y_1*y_4-y_2*y_4, y_9*y_10*y_11-y_9*y_10*y_12-y_9*y_11*y_12+y_10*y_11*y_12, y_3*y_4*y_11-y_3*y_4*y_12-y_3*y_11*y_12+y_4*y_11*y_12, y_3*y_4*y_9-y_3*y_4*y_10-y_3*y_9*y_10+y_4*y_9*y_10, y_3*y_4*y_7-y_3*y_4*y_8-y_3*y_7*y_8+y_4*y_7*y_8, y_1^2, y_2^2, y_3^2, y_4^2, y_5^2, y_6^2, y_7^2, y_8^2, y_9^2, y_10^2, y_11^2, y_12^2}})
AOTinIdeal = ideal map(R^1,R^{{-2}, {-2}, {-2}, {-2}, {-2}, {-2}, {-2}, {-2}, {-2}, {-2}, {-2}, {-2}, {-2}, {-2}, {-2}, {-2}, {-2}, {-3}, {-3}, {-3}, {-3}, {-3}, {-3}, {-3}, {-3}},{{y_12^2, y_11^2, y_10^2, y_9^2, y_8^2, y_6*y_8, y_5*y_8, y_7^2, y_6*y_7, y_5*y_7, y_6^2, y_5^2, y_4^2, y_3^2, y_2^2, y_1*y_2, y_1^2, y_9*y_10*y_11, y_7*y_8*y_11, y_3*y_4*y_11, y_5*y_6*y_10, y_7*y_8*y_9, y_5*y_6*y_9, y_3*y_4*y_9, y_3*y_4*y_7}})
G = graph {set {0, 3}, set {3, 6}, set {0, 5}, set {0, 6}, set {1, 4}, set {2, 4}, set {4, 5}, set {4, 6}, set {1, 5}, set {1, 6}, set {2, 5}, set {2, 6}}
