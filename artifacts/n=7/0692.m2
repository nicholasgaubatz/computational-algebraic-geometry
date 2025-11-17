                                                                                                                                                                                                                                                                                                                                                                                                                                                  2   2   2   2   2   2   2   2   2   2
HashTable{AOTideal => ideal (y y y  - y y y   - y y y   + y y y  , y y y  - y y y   - y y y   + y y y  , y y y  - y y y  - y y y  + y y y , y y y  - y y y   - y y y   + y y y  , y y y  - y y y  - y y y  + y y y , y y y y  - y y y y   - y y y y   + y y y y   + y y y y  , y y y y  - y y y y  - y y y y  + y y y y  + y y y y , y y y y  - y y y y  + y y y y  - y y y y  - y y y y , y y y y  - y y y y  + y y y y  - y y y y  - y y y y , y , y , y , y , y , y , y , y , y , y  )}
                              7 8 9    7 8 10    7 9 10    8 9 10   5 6 8    5 6 10    5 8 10    6 8 10   5 6 7    5 6 9    5 7 9    6 7 9   3 4 6    3 4 10    3 6 10    4 6 10   3 4 5    3 4 8    3 5 8    4 5 8   1 2 4 9    1 2 4 10    1 2 9 10    1 4 9 10    2 4 9 10   1 2 4 7    1 2 4 8    1 2 7 8    1 4 7 8    2 4 7 8   1 2 3 6    1 2 3 9    1 2 6 9    1 3 6 9    2 3 6 9   1 2 3 5    1 2 3 7    1 2 5 7    1 3 5 7    2 3 5 7   1   2   3   4   5   6   7   8   9   10
                                2    2   2   2   2   2   2   2   2   2
          AOTinIdeal => ideal (y  , y , y , y , y , y , y , y , y , y , y y y , y y y , y y y , y y y , y y y , y y y y , y y y y , y y y y , y y y y )
                                10   9   8   7   6   5   4   3   2   1   7 8 9   5 6 8   5 6 7   3 4 6   3 4 5   1 2 4 9   1 2 4 7   1 2 3 6   1 2 3 5
          graph => {set {0, 3}, set {3, 5}, set {0, 4}, set {0, 6}, set {1, 4}, set {2, 4}, set {1, 5}, set {1, 6}, set {2, 5}, set {2, 6}}
                                  2       3       4       5      6
          hSeries => 1 + 10T + 45T  + 115T  + 173T  + 142T  + 48T
          hyperplanes => {a - d, d - f, a - e, a - g, b - e, c - e, b - f, b - g, c - f, c - g}
          numVariables => 10
          WLPfull => "The AOT algebra has WLP"
          WLPin => "A does not have WLP at A_4"


R = QQ[y_1..y_10]
AOTideal = ideal map(R^1,R^{{-3}, {-3}, {-3}, {-3}, {-3}, {-4}, {-4}, {-4}, {-4}, {-2}, {-2}, {-2}, {-2}, {-2}, {-2}, {-2}, {-2}, {-2}, {-2}},{{y_7*y_8*y_9-y_7*y_8*y_10-y_7*y_9*y_10+y_8*y_9*y_10, y_5*y_6*y_8-y_5*y_6*y_10-y_5*y_8*y_10+y_6*y_8*y_10, y_5*y_6*y_7-y_5*y_6*y_9-y_5*y_7*y_9+y_6*y_7*y_9, y_3*y_4*y_6-y_3*y_4*y_10-y_3*y_6*y_10+y_4*y_6*y_10, y_3*y_4*y_5-y_3*y_4*y_8-y_3*y_5*y_8+y_4*y_5*y_8, y_1*y_2*y_4*y_9-y_1*y_2*y_4*y_10-y_1*y_2*y_9*y_10+y_1*y_4*y_9*y_10+y_2*y_4*y_9*y_10, y_1*y_2*y_4*y_7-y_1*y_2*y_4*y_8-y_1*y_2*y_7*y_8+y_1*y_4*y_7*y_8+y_2*y_4*y_7*y_8, y_1*y_2*y_3*y_6-y_1*y_2*y_3*y_9+y_1*y_2*y_6*y_9-y_1*y_3*y_6*y_9-y_2*y_3*y_6*y_9, y_1*y_2*y_3*y_5-y_1*y_2*y_3*y_7+y_1*y_2*y_5*y_7-y_1*y_3*y_5*y_7-y_2*y_3*y_5*y_7, y_1^2, y_2^2, y_3^2, y_4^2, y_5^2, y_6^2, y_7^2, y_8^2, y_9^2, y_10^2}})
AOTinIdeal = ideal map(R^1,R^{{-2}, {-2}, {-2}, {-2}, {-2}, {-2}, {-2}, {-2}, {-2}, {-2}, {-3}, {-3}, {-3}, {-3}, {-3}, {-4}, {-4}, {-4}, {-4}},{{y_10^2, y_9^2, y_8^2, y_7^2, y_6^2, y_5^2, y_4^2, y_3^2, y_2^2, y_1^2, y_7*y_8*y_9, y_5*y_6*y_8, y_5*y_6*y_7, y_3*y_4*y_6, y_3*y_4*y_5, y_1*y_2*y_4*y_9, y_1*y_2*y_4*y_7, y_1*y_2*y_3*y_6, y_1*y_2*y_3*y_5}})
G = graph {set {0, 3}, set {3, 5}, set {0, 4}, set {0, 6}, set {1, 4}, set {2, 4}, set {1, 5}, set {1, 6}, set {2, 5}, set {2, 6}}
