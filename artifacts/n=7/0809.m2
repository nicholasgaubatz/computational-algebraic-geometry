                                                                                                                                                                                                                             2   2   2   2   2   2   2   2   2   2
HashTable{AOTideal => ideal (y y  - y y  + y y , y y  - y y  - y y , y y y  - y y y  - y y y  + y y y , y y y y  - y y y y   - y y y y   + y y y y   - y y y y  , y y y y  - y y y y   + y y y y   - y y y y   - y y y y  , y , y , y , y , y , y , y , y , y , y  )}
                              4 5    4 9    5 9   2 3    2 6    3 6   1 2 5    1 2 7    1 5 7    2 5 7   6 7 8 9    6 7 8 10    6 7 9 10    6 8 9 10    7 8 9 10   1 3 4 8    1 3 4 10    1 3 8 10    1 4 8 10    3 4 8 10   1   2   3   4   5   6   7   8   9   10
                                2    2   2   2   2   2         2   2         2   2
          AOTinIdeal => ideal (y  , y , y , y , y , y , y y , y , y , y y , y , y , y y y , y y y y , y y y y , y y y y , y y y y , y y y y y , y y y y y , y y y y y )
                                10   9   8   7   6   5   4 5   4   3   2 3   2   1   1 2 5   6 7 8 9   1 3 4 8   1 2 4 7   1 3 5 6   1 3 5 8 9   1 2 4 6 8   1 3 4 6 7
          graph => {set {0, 3}, set {1, 3}, set {3, 5}, set {0, 4}, set {0, 6}, set {1, 5}, set {1, 6}, set {2, 4}, set {4, 6}, set {2, 5}}
                                  2       3       4       5      6
          hSeries => 1 + 10T + 43T  + 103T  + 146T  + 115T  + 38T
          hyperplanes => {a - d, b - d, d - f, a - e, a - g, b - f, b - g, c - e, e - g, c - f}
          numVariables => 10
          WLPfull => "The AOT algebra has WLP"
          WLPin => "The AOT algebra has WLP"


R = QQ[y_1..y_10]
AOTideal = ideal map(R^1,R^{{-2}, {-2}, {-3}, {-4}, {-4}, {-2}, {-2}, {-2}, {-2}, {-2}, {-2}, {-2}, {-2}, {-2}, {-2}},{{y_4*y_5-y_4*y_9+y_5*y_9, y_2*y_3-y_2*y_6-y_3*y_6, y_1*y_2*y_5-y_1*y_2*y_7-y_1*y_5*y_7+y_2*y_5*y_7, y_6*y_7*y_8*y_9-y_6*y_7*y_8*y_10-y_6*y_7*y_9*y_10+y_6*y_8*y_9*y_10-y_7*y_8*y_9*y_10, y_1*y_3*y_4*y_8-y_1*y_3*y_4*y_10+y_1*y_3*y_8*y_10-y_1*y_4*y_8*y_10-y_3*y_4*y_8*y_10, y_1^2, y_2^2, y_3^2, y_4^2, y_5^2, y_6^2, y_7^2, y_8^2, y_9^2, y_10^2}})
AOTinIdeal = ideal map(R^1,R^{{-2}, {-2}, {-2}, {-2}, {-2}, {-2}, {-2}, {-2}, {-2}, {-2}, {-2}, {-2}, {-3}, {-4}, {-4}, {-4}, {-4}, {-5}, {-5}, {-5}},{{y_10^2, y_9^2, y_8^2, y_7^2, y_6^2, y_5^2, y_4*y_5, y_4^2, y_3^2, y_2*y_3, y_2^2, y_1^2, y_1*y_2*y_5, y_6*y_7*y_8*y_9, y_1*y_3*y_4*y_8, y_1*y_2*y_4*y_7, y_1*y_3*y_5*y_6, y_1*y_3*y_5*y_8*y_9, y_1*y_2*y_4*y_6*y_8, y_1*y_3*y_4*y_6*y_7}})
G = graph {set {0, 3}, set {1, 3}, set {3, 5}, set {0, 4}, set {0, 6}, set {1, 5}, set {1, 6}, set {2, 4}, set {4, 6}, set {2, 5}}
