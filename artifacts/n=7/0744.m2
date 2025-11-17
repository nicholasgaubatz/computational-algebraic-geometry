                                                                                                                                                                                                                                                                                                                      2   2   2   2   2   2   2   2   2   2    2    2
HashTable{AOTideal => ideal (y y  - y y   - y y  , y y  - y y  + y y , y y  - y y  + y y , y y  - y y  - y y , y y  - y y  - y y , y y  - y y  - y y , y y y   - y y y   - y y  y   + y y  y  , y y y   - y y y   - y y  y   + y y  y  , y y y  - y y y   - y y y   + y y y  , y y y  - y y y   - y y y   + y y y  , y , y , y , y , y , y , y , y , y , y  , y  , y  )}
                              8 9    8 11    9 11   5 7    5 9    7 9   2 4    2 9    4 9   1 4    1 7    4 7   1 3    1 6    3 6   1 2    1 5    2 5   6 7 10    6 7 11    6 10 11    7 10 11   3 4 10    3 4 11    3 10 11    4 10 11   5 6 8    5 6 10    5 8 10    6 8 10   2 3 8    2 3 10    2 8 10    3 8 10   1   2   3   4   5   6   7   8   9   10   11   12
                                2    2    2    2         2   2         2   2   2               2         2         2
          AOTinIdeal => ideal (y  , y  , y  , y , y y , y , y , y y , y , y , y , y y , y y , y , y y , y , y y , y , y y y  , y y y  , y y y , y y y , y y y , y y y , y y y y  , y y y y  , y y y y )
                                12   11   10   9   8 9   8   7   5 7   6   5   4   2 4   1 4   3   1 3   2   1 2   1   6 7 10   3 4 10   5 6 8   2 3 8   3 4 6   2 3 5   5 6 9 10   2 3 9 10   2 3 6 7
          graph => {set {0, 3}, set {3, 4}, set {3, 5}, set {3, 6}, set {0, 4}, set {0, 5}, set {0, 6}, set {1, 4}, set {4, 6}, set {1, 5}, set {1, 6}, set {2, 6}}
                                  2       3       4       5      6
          hSeries => 1 + 12T + 60T  + 158T  + 227T  + 166T  + 48T
          hyperplanes => {a - d, d - e, d - f, d - g, a - e, a - f, a - g, b - e, e - g, b - f, b - g, c - g}
          numVariables => 12
          WLPfull => "The AOT algebra has WLP"
          WLPin => "The AOT algebra has WLP"


R = QQ[y_1..y_12]
AOTideal = ideal map(R^1,R^{{-2}, {-2}, {-2}, {-2}, {-2}, {-2}, {-3}, {-3}, {-3}, {-3}, {-2}, {-2}, {-2}, {-2}, {-2}, {-2}, {-2}, {-2}, {-2}, {-2}, {-2}, {-2}},{{y_8*y_9-y_8*y_11-y_9*y_11, y_5*y_7-y_5*y_9+y_7*y_9, y_2*y_4-y_2*y_9+y_4*y_9, y_1*y_4-y_1*y_7-y_4*y_7, y_1*y_3-y_1*y_6-y_3*y_6, y_1*y_2-y_1*y_5-y_2*y_5, y_6*y_7*y_10-y_6*y_7*y_11-y_6*y_10*y_11+y_7*y_10*y_11, y_3*y_4*y_10-y_3*y_4*y_11-y_3*y_10*y_11+y_4*y_10*y_11, y_5*y_6*y_8-y_5*y_6*y_10-y_5*y_8*y_10+y_6*y_8*y_10, y_2*y_3*y_8-y_2*y_3*y_10-y_2*y_8*y_10+y_3*y_8*y_10, y_1^2, y_2^2, y_3^2, y_4^2, y_5^2, y_6^2, y_7^2, y_8^2, y_9^2, y_10^2, y_11^2, y_12^2}})
AOTinIdeal = ideal map(R^1,R^{{-2}, {-2}, {-2}, {-2}, {-2}, {-2}, {-2}, {-2}, {-2}, {-2}, {-2}, {-2}, {-2}, {-2}, {-2}, {-2}, {-2}, {-2}, {-3}, {-3}, {-3}, {-3}, {-3}, {-3}, {-4}, {-4}, {-4}},{{y_12^2, y_11^2, y_10^2, y_9^2, y_8*y_9, y_8^2, y_7^2, y_5*y_7, y_6^2, y_5^2, y_4^2, y_2*y_4, y_1*y_4, y_3^2, y_1*y_3, y_2^2, y_1*y_2, y_1^2, y_6*y_7*y_10, y_3*y_4*y_10, y_5*y_6*y_8, y_2*y_3*y_8, y_3*y_4*y_6, y_2*y_3*y_5, y_5*y_6*y_9*y_10, y_2*y_3*y_9*y_10, y_2*y_3*y_6*y_7}})
G = graph {set {0, 3}, set {3, 4}, set {3, 5}, set {3, 6}, set {0, 4}, set {0, 5}, set {0, 6}, set {1, 4}, set {4, 6}, set {1, 5}, set {1, 6}, set {2, 6}}
