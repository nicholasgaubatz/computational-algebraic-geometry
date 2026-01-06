                                                                                                                                                                                                                                                                                                                                                                           2   2   2   2   2   2   2   2   2   2    2    2
HashTable{AOTideal => ideal (y  y   - y  y   + y  y  , y y  - y y   + y y  , y y  - y y  - y y , y y  - y y  - y y , y y y  - y y y   - y y y   + y y y  , y y y  - y y y   - y y y   + y y y  , y y y  - y y y   - y y y   + y y y  , y y y  + y y y   - y y y   - y y y  , y y y  - y y y  - y y y  + y y y , y y y y  - y y y y   - y y y y   + y y y y   + y y y y  , y , y , y , y , y , y , y , y , y , y  , y  , y  )}
                              10 11    10 12    11 12   6 7    6 12    7 12   1 4    1 7    4 7   1 3    1 5    3 5   5 7 9    5 7 11    5 9 11    7 9 11   5 6 9    5 6 10    5 9 10    6 9 10   3 4 9    3 4 11    3 9 11    4 9 11   2 4 8    2 4 12    2 8 12    4 8 12   1 2 6    1 2 8    1 6 8    2 6 8   2 3 8 9    2 3 8 10    2 3 9 10    2 8 9 10    3 8 9 10   1   2   3   4   5   6   7   8   9   10   11   12
                                2    2            2    2   2   2         2   2   2         2         2   2
          AOTinIdeal => ideal (y  , y  , y  y  , y  , y , y , y , y y , y , y , y , y y , y , y y , y , y , y y y , y y y , y y y , y y y , y y y , y y y , y y y y , y y y y , y y y y , y y y y y , y y y y y )
                                12   11   10 11   10   9   8   7   6 7   6   5   4   1 4   3   1 3   2   1   5 7 9   5 6 9   3 4 9   2 4 8   1 2 6   3 4 5   2 3 8 9   1 2 7 8   2 3 5 6   1 2 5 8 9   2 3 5 7 8
          graph => {set {0, 3}, set {1, 3}, set {3, 4}, set {3, 6}, set {0, 4}, set {0, 5}, set {0, 6}, set {1, 5}, set {2, 4}, set {2, 5}, set {2, 6}, set {5, 6}}
                                  2       3       4       5      6
          hSeries => 1 + 12T + 62T  + 175T  + 281T  + 239T  + 82T
          hyperplanes => {a - d, b - d, d - e, d - g, a - e, a - f, a - g, b - f, c - e, c - f, c - g, f - g}
          numVariables => 12
          WLPfull => "The AOT algebra has WLP"
          WLPin => "A does not have WLP at A_4"


R = QQ[y_1..y_12]
AOTideal = ideal map(R^1,R^{{-2}, {-2}, {-2}, {-2}, {-3}, {-3}, {-3}, {-3}, {-3}, {-4}, {-2}, {-2}, {-2}, {-2}, {-2}, {-2}, {-2}, {-2}, {-2}, {-2}, {-2}, {-2}},{{y_10*y_11-y_10*y_12+y_11*y_12, y_6*y_7-y_6*y_12+y_7*y_12, y_1*y_4-y_1*y_7-y_4*y_7, y_1*y_3-y_1*y_5-y_3*y_5, y_5*y_7*y_9-y_5*y_7*y_11-y_5*y_9*y_11+y_7*y_9*y_11, y_5*y_6*y_9-y_5*y_6*y_10-y_5*y_9*y_10+y_6*y_9*y_10, y_3*y_4*y_9-y_3*y_4*y_11-y_3*y_9*y_11+y_4*y_9*y_11, y_2*y_4*y_8+y_2*y_4*y_12-y_2*y_8*y_12-y_4*y_8*y_12, y_1*y_2*y_6-y_1*y_2*y_8-y_1*y_6*y_8+y_2*y_6*y_8, y_2*y_3*y_8*y_9-y_2*y_3*y_8*y_10-y_2*y_3*y_9*y_10+y_2*y_8*y_9*y_10+y_3*y_8*y_9*y_10, y_1^2, y_2^2, y_3^2, y_4^2, y_5^2, y_6^2, y_7^2, y_8^2, y_9^2, y_10^2, y_11^2, y_12^2}})
AOTinIdeal = ideal map(R^1,R^{{-2}, {-2}, {-2}, {-2}, {-2}, {-2}, {-2}, {-2}, {-2}, {-2}, {-2}, {-2}, {-2}, {-2}, {-2}, {-2}, {-3}, {-3}, {-3}, {-3}, {-3}, {-3}, {-4}, {-4}, {-4}, {-5}, {-5}},{{y_12^2, y_11^2, y_10*y_11, y_10^2, y_9^2, y_8^2, y_7^2, y_6*y_7, y_6^2, y_5^2, y_4^2, y_1*y_4, y_3^2, y_1*y_3, y_2^2, y_1^2, y_5*y_7*y_9, y_5*y_6*y_9, y_3*y_4*y_9, y_2*y_4*y_8, y_1*y_2*y_6, y_3*y_4*y_5, y_2*y_3*y_8*y_9, y_1*y_2*y_7*y_8, y_2*y_3*y_5*y_6, y_1*y_2*y_5*y_8*y_9, y_2*y_3*y_5*y_7*y_8}})
G = graph {set {0, 3}, set {1, 3}, set {3, 4}, set {3, 6}, set {0, 4}, set {0, 5}, set {0, 6}, set {1, 5}, set {2, 4}, set {2, 5}, set {2, 6}, set {5, 6}}
