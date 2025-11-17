                                                                                          2   2   2   2   2   2   2   2   2
HashTable{AOTideal => ideal (y y  - y y  - y y , y y  - y y  - y y , y y  - y y  - y y , y , y , y , y , y , y , y , y , y )   }
                              3 5    3 8    5 8   2 5    2 7    5 7   1 5    1 6    5 6   1   2   3   4   5   6   7   8   9
                                2   2   2   2   2                     2   2   2   2
          AOTinIdeal => ideal (y , y , y , y , y , y y , y y , y y , y , y , y , y , y y y , y y y , y y y )
                                9   8   7   6   5   3 5   2 5   1 5   4   3   2   1   2 3 7   1 3 6   1 2 6
          graph => {set {0, 5}, set {1, 5}, set {2, 5}, set {3, 5}, set {5, 6}, set {0, 6}, set {1, 6}, set {2, 6}, set {4, 6}}
                                 2      3      4      5     6
          hSeries => 1 + 9T + 33T  + 63T  + 66T  + 36T  + 8T
          hyperplanes => {a - f, b - f, c - f, d - f, f - g, a - g, b - g, c - g, e - g}
          numVariables => 9
          WLPfull => "The AOT algebra has WLP"
          WLPin => "A does not have WLP at A_3"


R = QQ[y_1..y_9]
AOTideal = ideal map(R^1,R^{{-2}, {-2}, {-2}, {-2}, {-2}, {-2}, {-2}, {-2}, {-2}, {-2}, {-2}, {-2}},{{y_3*y_5-y_3*y_8-y_5*y_8, y_2*y_5-y_2*y_7-y_5*y_7, y_1*y_5-y_1*y_6-y_5*y_6, y_1^2, y_2^2, y_3^2, y_4^2, y_5^2, y_6^2, y_7^2, y_8^2, y_9^2}})
AOTinIdeal = ideal map(R^1,R^{{-2}, {-2}, {-2}, {-2}, {-2}, {-2}, {-2}, {-2}, {-2}, {-2}, {-2}, {-2}, {-3}, {-3}, {-3}},{{y_9^2, y_8^2, y_7^2, y_6^2, y_5^2, y_3*y_5, y_2*y_5, y_1*y_5, y_4^2, y_3^2, y_2^2, y_1^2, y_2*y_3*y_7, y_1*y_3*y_6, y_1*y_2*y_6}})
G = graph {set {0, 5}, set {1, 5}, set {2, 5}, set {3, 5}, set {5, 6}, set {0, 6}, set {1, 6}, set {2, 6}, set {4, 6}}
