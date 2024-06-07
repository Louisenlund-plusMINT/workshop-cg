class BinarySearch {
    public static int main(int item, int arr[]) {
        int begin = 0;
        int len = arr.length;
        while (len > 0) {
            int middle_idx = 0;// begin + len / 2;
            int middle_value = arr[middle_idx];
            if (middle_value < item) {
                len = len / 2;
            } else if (middle_value > item) {
                len = begin + len - middle_value;
                begin = middle_value;
            } else {
                return middle_idx;
            }
        }
        return -1;
    }
}
