using System;
using System.Collections.Generic;
using System.ComponentModel;
using System.Drawing;
using System.Linq;
using System.Text;
using System.Windows.Threading;
using System.Windows.Forms;
using System.IO;
using System.IO.Ports;
using Thorlabs.TSI.ColorInterfaces;
using Thorlabs.TSI.ColorProcessor;
using Thorlabs.TSI.CoreInterfaces;
using Thorlabs.TSI.Demosaicker;
using Thorlabs.TSI.ImageData;
using Thorlabs.TSI.ImageDataInterfaces;
using Thorlabs.TSI.TLCamera;
using Thorlabs.TSI.TLCameraInterfaces;
using OpenCvSharp;
using System.Xml;
using System.Diagnostics;

namespace AAVLC_50m
{

    public partial class AAVLC_50m : Form , IDisposable
{
       
        private class LockableSharedData
        {
            // 每收到一帧，置为真，用于更新UI判别。
            public bool IsUpdateUIRequested;

            // BGR raw data and information on how to interpret it.
            public ImageDataUShort1D LatestImageData;
        }

        private class Flags
        {
            public bool check = false, corre = false;                       //check用于开始对准的标志，corre用于校对参数的标志
            public bool LD_finded = false, X_finded = false;                //光斑、标志寻找结果 flag
            public bool goal_miss = true, halo = false, on_move = false;    //目标丢失状态、处于光晕影响状态、目标处于运动状态 flag
            public bool cover = false;                                      //覆盖判别标志
            public bool mirror_recieved = true;                             //是否已振镜控制返回信号
            public bool PID = true;                                         //是否启用PID控制
            public bool kalman = false;                                     //是否启用卡尔曼滤波器
            public bool move_test = false;                                  //是否在进行移动对准性能测试
        }


        private readonly DispatcherTimer _dispatcherTimerUpdateUI = new DispatcherTimer();  
        private LockableSharedData _lockableSharedData = new LockableSharedData();

        private Bitmap _latestProcessBitmap, _latestDisplayBitmap;
        //private Bitmap processBitmap;
        private ITLCameraSDK _tlCameraSDK;
        private ITLCamera _tlCamera;//相机类
        //相机参数
        private ushort[] _demosaickedData = null;                               //用于保存demosaick后数据
        private ushort[] _processedImage = null;                                //用于保存颜色处理后的数据
        private Demosaicker _demosaicker = new Demosaicker();                   //demosaick处理器
        private ColorFilterArrayPhase _colorFilterArrayPhase;
        private ColorProcessor _colorProcessor = null;
        private bool _isColor = false;
        private ColorProcessorSDK _colorProcessorSDK = null;
        private uint expose_time = 10000;                                       //相机曝光时间
        private static uint bin = 1;
        //private double frame_rate = 30;                                       //相机帧率


        private int deviceNumber;                                               //连接相机设备数量
        private System.Drawing.Point center = new System.Drawing.Point(0, 0);   //图片上标志物中心坐标
        int width, height,start_x,start_y;                                      //图片宽度、图片高度

        /*串口通信参数*/
        private SerialPort com;
        private int ser_portsNumber;


        /*相机参数计算参数*/
        private static double pixel_size_x = 0.00345 * bin;                 //像素x方向尺寸（mm）
        private static double pixel_size_y = 0.00345 * bin;                 //像素y方向尺寸（mm）
        private double std_D = 710, std_R = 20;                             //实现距离粗测，根据圆环尺寸简单线性计算距离，此两个参数需要进一步测量
        private double Distance = 710;                                      //接收机平面距离相机焦平面距离（mm）                   需测量
        private double Focal_length = 16;                                   //固定焦距16mm

        private double Xc, Yc, Zc;                                          //相机坐标下目标位置(LED灯)
        private double Xc2center, Yc2center, Zc2center;                     //世界坐标系下，标识物中心到接收机中心距离，接收机中心-标识物中心
        private int delt_X_c2c, delt_Y_c2c;                                 //图像坐标系下，标识物中心到接收机中心距离，接收机中心-标识物中心

        private double Xm = 35, Ym = -42, Zm = 164;                         //相机坐标下振镜位置(上方镜片中心，mm)
        private double H_m12 = 15;                                          //振镜镜片高度差(mm)                                     需测量
        private double thelt1 = Math.PI / 4, thelt2 = Math.PI / 4;          //相机镜片偏转角度
        private int frame_counter_X, frame_counter_LD;                      //用来作计数器，每多少个帧处理后发一次振镜信号，作为显示两个线程处理速度比较
        private int send_test;                                              //仅串口通信测试时使用，后续弃用
        private int fail_counter = 5;                                       //寻找标志失败允许的次数，超过九开始局部寻找
        private XmlNodeList nodeList;
        XmlDocument xmlDoc;

        /*单次搜索的相关参数*/
        private int win_LD = 32;                                            //LD扫描窗尺寸，60（圆环1）,全
        private System.Drawing.Point LD = new System.Drawing.Point(0, 0);
        private int win_center = 15;                                        //中心覆盖啊区域窗尺寸，半
        private double LD_thre = 0.10;                                      //LD判别阈值
        //private Queue<long> Q_time;                                       //队列，保存移动时处理图片得到结果的时间
        //private Queue<double[]> Q_location;                               //队列，保存移动时处理图片得到的坐标
        private int move_counter;                                           //用于计数，辅助移动判别。
        //OpenCvSharp.Tracking.TrackerKCF tracker;                          //KCF追踪器
        //OpenCvSharp.Point[][] contours = new OpenCvSharp.Point[5][];      //连通域处理结果保存
        HierarchyIndex[] hier = new HierarchyIndex[5];
        int[] added_bias = new int[4] { 0, 0, 0, 0 };

        /*振镜控制参数*/
        System.Timers.Timer mirror_clock,fps_clock;
        int T_mirror = 10,T_fps = 1000;                                     //振镜定时时间100ms
        int frame_X_last, frame_LD_last, fps_X, fps_LD = 0;
        double delt_x1, delt_y1, delt_x2, delt_y2;                          //上一次执行时的偏差，进行微分控制
        double kp = 0.0002, ki, kd = 0.0001;                                //0.0002，0.0001，PID算法参数
        //int frame_record;
        //double[] delt_th;

        //多线程控制参数
        private delegate void find_process(ref Mat mat_pass);               //委托，两个寻找方法委托类型相同
        find_process _delegate_get_X, _delegate_get_LD;                     //两个委托，分别对应标志寻找和光斑寻找
        private IAsyncResult iar_X, iar_LD,iar_connect;                     //两个线程操作的状态检测
        private delegate ITLCamera connet_camera(String serial_nam, bool we);
        connet_camera _delegate_connect_camera;

        /*opencvsharp部分参数*/
        private CircleSegment[] circles, circles_temp;                      //用于存储寻找标志结果，采用均值方法降低波动
        private Queue<OpenCvSharp.Point> Q_center;                          //图像坐标系下中心坐标队列
        //private bool flag_cover = false;                                  //覆盖判别标志
        private double cover_thre = 0.78;                                   //覆盖判别阈值
        private int r = 70;

        /*卡尔曼滤波参数*/
        int num_kals = 5;                                                   //卡尔曼滤波器数量  
        List<OpenCvSharp.KalmanFilter> Kals;                    
        //OpenCvSharp.KalmanFilter kalmanfilter;
        Mat last_measurement, current_measurement,                          //上一时刻及当前时刻的测量值、预测值
            last_prediction, current_prediction, frame;
        int state_num = 4;                                                  //卡尔曼滤波状态数，与矩阵形状确定相关
        float err;
        List<float> err_list = new List<float>(100);                        //预测和实测误差列表
        private System.Drawing.Point prediction = new System.Drawing.Point(0, 0);

        private Flags flags;
        Stopwatch sw_1, sw_2;

        public AAVLC_50m()
        {
            this.InitializeComponent();
            //初始化圆环中心坐标队列
            Q_center = new Queue<OpenCvSharp.Point>();
            //Q_location = new Queue<double[]>();
            //Q_time = new Queue<long>();


            circles = new CircleSegment[1];
            //读取部分计算参数
            xml_reader();
            numericUpDown1.Value = Convert.ToDecimal(expose_time);
            numericUpDown3.Value = Convert.ToDecimal(win_center);
            numericUpDown5.Value = Convert.ToDecimal(win_LD);
            numericUpDown6.Value = Convert.ToDecimal(cover_thre);
            numericUpDown7.Value = Convert.ToDecimal(Distance);
            numericUpDown8.Value = Convert.ToDecimal(Zm);
            numericUpDown11.Value = Convert.ToDecimal(Xm);
            numericUpDown12.Value = Convert.ToDecimal(Ym);
            numericUpDown9.Value = Convert.ToDecimal(delt_X_c2c);
            numericUpDown10.Value = Convert.ToDecimal(delt_Y_c2c);
            numericUpDown15.Value = Convert.ToDecimal(added_bias[0]);
            numericUpDown16.Value = Convert.ToDecimal(added_bias[2]);
            numericUpDown17.Value = Convert.ToDecimal(num_kals);

            //kalman滤波器初始化
            kalman_init();

            System.Windows.Forms.Control.CheckForIllegalCrossThreadCalls = false;

            flags = new Flags();
            sw_1 = new Stopwatch();
            sw_1.Start();
        }


        private void refreshDeviceList()
        {
            /*更新相机列表*/
            camera_list.Items.Clear();
            if (this._tlCameraSDK == null)
                this._tlCameraSDK = TLCameraSDK.OpenTLCameraSDK();             
            var serialNumbers = this._tlCameraSDK.DiscoverAvailableCameras();       //获得视频设备列表
            deviceNumber = serialNumbers.Count;                                     //获取设备数量
            /*尝试连接设备*/
            try
            {
                if (deviceNumber == 0)
                    throw new ApplicationException();                               //没有设备返回异常
                foreach (String device in serialNumbers)                            //tCombo得到各设备名称
                    camera_list.Items.Add(device);                                  //添加入tCombo
                camera_list.SelectedIndex = 0;                                      //默认序号为0
            }
            catch (ApplicationException)
            {
                MessageBox.Show("No Thorlabs camera detected.");
            }

            /*更新串口列表*/
            SerialPort_list.Items.Clear();
            string[] portlist = System.IO.Ports.SerialPort.GetPortNames();          //获取串口名称列表
            ser_portsNumber = portlist.Length;
            for (int i = 0; i < ser_portsNumber; i++)
            {
                string name = portlist[i];                                          //依次添加串口到ui列表中
                SerialPort_list.Items.Add(name);
            }
            if (portlist.Length != 0)
            {
                SerialPort_list.SelectedIndex = 0;                                  //默认序号为0
            }
        }

        void  IDisposable.Dispose()
        {
            xml_writer();                                                           //保存相关参数到xml文件中
            try
            {
                if (this._dispatcherTimerUpdateUI != null)
                {
                    this._dispatcherTimerUpdateUI.Stop();                                       //更新用户界面定时器停止
                    this._dispatcherTimerUpdateUI.Tick -= this.DispatcherTimerUpdateUI_Tick;    //删去订阅函数
                }

                if (this._tlCameraSDK != null && this._tlCamera != null)
                {
                    if (this._tlCamera.IsArmed)
                    {
                        this._tlCamera.Disarm();                                                //解除相机连接
                    }

                    this._tlCamera.Dispose();                                                   //相机释放
                    this._tlCamera = null;

                    if (this._colorProcessor != null)
                    {
                        this._colorProcessor.Dispose();                                         //颜色处理器释放
                        this._colorProcessor = null;        
                    }

                    if (this._colorProcessorSDK != null)
                    {
                        this._colorProcessorSDK.Dispose();                                      //颜色处理工具包释放
                        this._colorProcessorSDK = null;
                    }

                    this._tlCameraSDK.Dispose();                                                //相机工具包释放
                    this._tlCameraSDK = null;
                }

                if (this.com != null)
                {
                    com.Close();                                                                //关闭串口
                    this.com = null;
                }
            }
            catch (Exception exception)
            {
                MessageBox.Show(exception.Message);
            }
            this.Dispose(true);
            GC.SuppressFinalize(this);
        }

        protected override void OnClosing(CancelEventArgs e)
        {//计算总的预测误差
            float sum_err = 0;
            for (int i = 10; i < err_list.Count; i++)
            {
                sum_err += err_list.ElementAt<float>(i);                                        //误差求和
                Console.Write(err_list.ElementAt<float>(i) + " ");
            }
            Console.WriteLine("\r\n" + "均方根误差均值" + sum_err / (err_list.Count - 10));        

            xml_writer();                                                                       //保存相关参数到xml文件中

            try
            {
                if (this._dispatcherTimerUpdateUI != null)
                {
                    this._dispatcherTimerUpdateUI.Stop();                                       //更新用户界面定时器停止
                    this._dispatcherTimerUpdateUI.Tick -= this.DispatcherTimerUpdateUI_Tick;    //删除更新的订阅
                }

                if (this._tlCameraSDK != null && this._tlCamera != null)
                {
                    if (this._tlCamera.IsArmed)
                    {
                        this._tlCamera.Disarm();                                                //释放相机调用
                    }
                    this._tlCamera.Dispose();                                                   //释放相机
                    this._tlCamera = null;

                    if (this._colorProcessor != null)
                    {
                        this._colorProcessor.Dispose();                                         //释放颜色处理器
                        this._colorProcessor = null;
                    }

                    if (this._colorProcessorSDK != null)
                    {
                        this._colorProcessorSDK.Dispose();                                      //释放颜色处理包
                        this._colorProcessorSDK = null;
                    }

                    this._tlCameraSDK.Dispose();                                                //释放相机工具包
                    this._tlCameraSDK = null;
                }

                if (this.com != null)
                {
                    com.Close();                                                                //关闭串口
                    this.com = null;
                }
                if (mirror_clock != null)
                {
                    mirror_clock.Stop();                                                        //振镜控制的定时器停止
                }
                if (fps_clock !=null)
                {
                    fps_clock.Stop();                                                           //帧率计算的定时器停止
                }
            }
            catch (Exception exception)
            {
                MessageBox.Show(exception.Message);
            }

            base.OnClosing(e);
        }

        //[System.Runtime.ExceptionServices.HandleProcessCorruptedStateExceptions]
        private void  button1_Click(object sender, EventArgs e)
        {
            //获取指定视频设备
            if (deviceNumber > 0)
            {
            //IntPtr stringPointer = (IntPtr)Marshal.StringToHGlobalAnsi(camera_selected);

                try
                {
                    _delegate_connect_camera = new connet_camera(this._tlCameraSDK.OpenCamera);     
                    var serialNumbers = this._tlCameraSDK.DiscoverAvailableCameras();               //搜索可用相机

                    
                    char[] temp= camera_list.Text.ToCharArray();
                    String camera_selected = new String(temp);                                      //获取连接相机名称
                        
                    this._tlCamera = this._tlCameraSDK.OpenCamera(camera_selected, true);           //打开指定相机

                }
                catch (Exception exception)
                {
                    MessageBox.Show("Connection falied.\nPlease try again." + exception.Message);
                    //Environment.Exit(0);
                }
                /*一些参数设置*/
                #region ROI设置
                _tlCamera.ROIAndBin = new Thorlabs.TSI.TLCameraInterfaces.ROIAndBin()       //设置ROI，即感兴趣区域
                                             { ROIOriginX_pixels = 0, ROIOriginY_pixels = 0, 
                                                ROIHeight_pixels = 1080, ROIWidth_pixels = 1440, 
                                                BinX = bin, BinY = bin };
                    
                width = (int)_tlCamera.ROIAndBin.ROIWidth_pixels;                           //获取图片的尺寸
                height =(int)_tlCamera.ROIAndBin.ROIHeight_pixels;
                start_x = (int)_tlCamera.ROIAndBin.ROIOriginX_pixels;                       //获取图片的起始坐标
                start_y = (int)_tlCamera.ROIAndBin.ROIOriginY_pixels;
                #endregion

                //uint t = _tlCamera.SensorReadoutTime_ns;      

                #region 帧率查看、设置
                // this._tlCamera.FramesPerTrigger_zeroForUnlimited = 0;
                //Range<double> fps_range = this._tlCamera.FrameRateControlValueRange_fps;
                //this._tlCamera.IsFrameRateControlEnabled = true;
                //this._tlCamera.FrameRateControlValue_fps = fps_range.Maximum; //设置帧率为20，范围 0.944-34.815
                #endregion

                #region 曝光时间、增益、黑电平设置
                this._tlCamera.ExposureTime_us = expose_time;                               //设置曝光时长，59-26843404 us,初始50000，后设100

                if (this._tlCamera.GainRange.Maximum > 0)
                {
                    const double gainDb = 6.0;//6.0
                    var gainIndex = this._tlCamera.ConvertDecibelsToGain(gainDb);           //相机增益
                    this._tlCamera.Gain = gainIndex;
                }
                if (this._tlCamera.BlackLevelRange.Maximum > 0)
                {
                    this._tlCamera.BlackLevel = 0;                                          //相机黑电平，初始48
                }
                #endregion

                #region 颜色处理部分设置
                this._isColor = bin == 1;// this._tlCamera.CameraSensorType == CameraSensorType.Bayer;
                if (this._isColor)
                {
                    this._colorProcessorSDK = new ColorProcessorSDK();
                    this._colorFilterArrayPhase = this._tlCamera.ColorFilterArrayPhase;
                    var colorCorrectionMatrix = this._tlCamera.GetCameraColorCorrectionMatrix();
                    var whiteBalanceMatrix = this._tlCamera.GetDefaultWhiteBalanceMatrix();
                    //this._colorProcessor = (ColorProcessor)this._colorProcessorSDK.CreateColorProcessor();
                    this._colorProcessor = (ColorProcessor)this._colorProcessorSDK.CreateStandardRGBColorProcessor(whiteBalanceMatrix, colorCorrectionMatrix, (int)this._tlCamera.BitDepth);
                }
                #endregion

                this._tlCamera.OnImageFrameAvailable += this.OnImageFrameAvailable;                     //设置帧到达回调函数
                this._tlCamera.OperationMode = OperationMode.SoftwareTriggered;                         //设置触发模式，软件触发
                this._tlCamera.Arm();                                                                   
                this._tlCamera.IssueSoftwareTrigger();                                                  
                this._dispatcherTimerUpdateUI.Interval = TimeSpan.FromMilliseconds(20);                 //UI更新间隔设置（ms）
                this._dispatcherTimerUpdateUI.Tick += this.DispatcherTimerUpdateUI_Tick;                //处理方式
                this._dispatcherTimerUpdateUI.Start();
            }
            else
            {
                MessageBox.Show("No Thorlabs camera selected.");
            }
        }


        private void Form2_Load(object sender, EventArgs e)
        {
            refreshDeviceList();                                            //窗体加载时，更新下拉列表里的设备
        }


        /*相机轮询调用函数，图片帧处理，调用坐标计算、角度计算、串口信号发送*/
        private void DispatcherTimerUpdateUI_Tick(object sender, EventArgs e)
        {
            lock (this._lockableSharedData)
            {
                if (this._lockableSharedData.IsUpdateUIRequested)
                {
                    if (this._latestDisplayBitmap != null)
                    {
                        this._latestDisplayBitmap.Dispose();
                        this._latestDisplayBitmap = null;
                    }

                    this._latestDisplayBitmap = this._lockableSharedData.LatestImageData.ToBitmap_Format24bppRgb();

                    this.pictureBoxLiveImage.Invalidate();
                    this._lockableSharedData.IsUpdateUIRequested = false;
                }
            }
        }
                       

        //此函数用于图像处理回调
        private void OnImageFrameAvailable(ITLCamera sender, EventArgs eventargs)
        {
            lock (this._lockableSharedData)
            {
                var frame = sender.GetPendingFrameOrNull();                     //获取新帧
                if (frame != null)
                {
                    if (this._isColor)                                          //此处根据相机类型进行处理，实验中固定采用彩色相机
                    {
                        var rawData = ((IImageDataUShort1D)frame.ImageData).ImageData_monoOrBGR;
                        var size = frame.ImageData.Width_pixels * frame.ImageData.Height_pixels * 3;
                        if ((this._demosaickedData == null) || (size != this._demosaickedData.Length))
                        {
                            this._demosaickedData = new ushort[frame.ImageData.Width_pixels * frame.ImageData.Height_pixels * 3];
                        }
                        this._demosaicker.Demosaic(frame.ImageData.Width_pixels, frame.ImageData.Height_pixels, 0, 0, this._colorFilterArrayPhase, ColorFormat.BGRPixel, ColorSensorType.Bayer, frame.ImageData.BitDepth, rawData, this._demosaickedData);

                        if ((this._processedImage == null) || (size != this._demosaickedData.Length))
                        {
                            this._processedImage = new ushort[frame.ImageData.Width_pixels * frame.ImageData.Height_pixels * 3];
                        }

                        ushort maxValue = (ushort)((1 << frame.ImageData.BitDepth) - 1);
                        this._colorProcessor.Transform48To48(_demosaickedData, ColorFormat.BGRPixel, 0, maxValue, 0, maxValue, 0, maxValue, 0, 0, 0, this._processedImage, ColorFormat.BGRPixel);
                        this._lockableSharedData.LatestImageData = new ImageDataUShort1D(_processedImage, frame.ImageData.Width_pixels, frame.ImageData.Height_pixels, frame.ImageData.BitDepth, ImageDataFormat.BGRPixel);
                        this._lockableSharedData.IsUpdateUIRequested = true;

                        if(_latestProcessBitmap == null)
                        {
                            _latestProcessBitmap = this._lockableSharedData.LatestImageData.ToBitmap_Format24bppRgb();
                        }
                        else
                        {
                            lock(_latestProcessBitmap)
                            {
                             _latestProcessBitmap = this._lockableSharedData.LatestImageData.ToBitmap_Format24bppRgb();
                            }
                        }
                        
                    }
                    //对于相机颜色类型判断，黑白相机处理在此处添加

                    #region 开始对准的线程建立
                    if (flags.check)                                                                        //点击对准按钮，开始对准
                    {
                        Mat srcmat = OpenCvSharp.Extensions.BitmapConverter.ToMat(_latestProcessBitmap);    //将bitmap数据转换成Opencv中矩阵形势

                        if (_delegate_get_X == null)                                                        //标志寻找线程建立
                        {
                            _delegate_get_X = new find_process(process_getX);                               //第一次寻找时，初始化委托
                            iar_X = _delegate_get_X.BeginInvoke(ref srcmat, null, null);                    
                        }
                        else if (iar_X.IsCompleted)
                        {
                            iar_X = _delegate_get_X.BeginInvoke(ref srcmat, null, null);                    //寻找线程运行结束，再开始下一次寻找
                            checkBox1.Checked = flags.X_finded; ;                                           //更新对准标志（或可单独分离至用户界面更新部分）
                        }

                        if (_delegate_get_LD == null)                                                       //寻找光斑新建线程
                        {
                            _delegate_get_LD = new find_process(process_getLD);                             //第一次寻找时，初始化委托（无论标志寻找结果，均运行）
                            iar_LD = _delegate_get_LD.BeginInvoke(ref srcmat, null, null);
                        }
                        else if (iar_LD.IsCompleted && flags.mirror_recieved)
                        {                                                        //每次LD识别需要在上一次线程结束并且振镜控制结束之后
                            iar_LD = _delegate_get_LD.BeginInvoke(ref srcmat, null, null);
                        }
                    }
                    #endregion
                }
            }
        }

        private void button4_Click(object sender, EventArgs e)
        {
            refreshDeviceList();//更新下拉列表里的设备
        }


        /*串口连接按钮*/
        private void button3_Click(object sender, EventArgs e)
        {
            if (ser_portsNumber > 0)
            {
                if (com != null && com.IsOpen)
                {
                    com.Close();
                    com = null;
                }
                com = new SerialPort();
                com.BaudRate = 115200;                          //串口波特率设置
                com.PortName = SerialPort_list.Text;            //连接串口名称
                com.DataBits = 8;                               //数据位数
                com.StopBits = System.IO.Ports.StopBits.One;    //停止位设置
                com.Open();                                     //串口打开

                this.com.DataReceived += new System.IO.Ports.SerialDataReceivedEventHandler(this.OnDataReceived);//设置串口返回信息处理回调函数
            }
            else
            {
                MessageBox.Show("No Serial Port selected.");
            }
        }

        private void pictureBoxLiveImage_Paint(object sender, PaintEventArgs e)
        {//展示相机采集图片，并在图片上标识相关信，展示在UI界面上
            if (this._latestDisplayBitmap != null)
            {
                var scale = Math.Min((float)this.pictureBoxLiveImage.Width / this._latestDisplayBitmap.Width, (float)this.pictureBoxLiveImage.Height / this._latestDisplayBitmap.Height);
                e.Graphics.DrawImage(this._latestDisplayBitmap, new RectangleF(0, 0, 
                this._latestDisplayBitmap.Width * scale, this._latestDisplayBitmap.Height * scale));    //绘制采集图像
                /*绘制目标中心以及边框  以及覆盖判别中心区域*/
                if(flags.X_finded)
                {
                    e.Graphics.FillEllipse(Brushes.Blue, (center.X +delt_X_c2c + width / 2) * scale - 1, 
                        (center.Y + delt_Y_c2c + height / 2) * scale - 1, 3, 3);                        //绘制标志中心
                    e.Graphics.DrawRectangle(new Pen(Color.Red, 1),
                         new System.Drawing.Rectangle((int)((center.X + width / 2 - r) * scale), 
                         (int)((center.Y + height / 2 - r) * scale), (int)(2 * r * scale), 
                         (int)(2 * r * scale)));                                                        //红色，绘制标志物轮廓矩形
                    e.Graphics.DrawRectangle(new Pen(Color.Black, 1),
                        new System.Drawing.Rectangle((int)((center.X + width / 2 + delt_X_c2c - win_center) * scale),
                        (int)((center.Y + height / 2 +delt_Y_c2c - win_center) * scale), (int)((2 * win_center + 1) * scale),
                        (int)((2 * win_center + 1) * scale)));                                          //红色，绘制标志物轮廓矩形

                }
                /*绘制激光光斑中心以及边框*/
                if(flags.LD_finded)
                {
                    e.Graphics.FillEllipse(Brushes.Green,
                        (LD.X + width / 2) * scale - 1, (LD.Y + height / 2) * scale - 1, 3, 3);         //绘制LD光斑中心
                    e.Graphics.DrawRectangle(new Pen(Color.Green, 1),
                        new System.Drawing.Rectangle((int)((LD.X + width / 2 - win_LD / 2 ) * scale)+1,
                        (int)((LD.Y + height / 2 - win_LD / 2) * scale)+1, (int)(win_LD * scale),
                        (int)(win_LD * scale)));                                                        //绿色，绘制标志物轮廓矩形
                }

                /*UI界面上的信息更新*/
                textBox7.Text = frame_counter_LD.ToString();                    //光斑识别成功的帧数
                textBox3.Text = frame_counter_X.ToString();                     //标识物识别成功的帧数
                textBox4.Text = fps_X.ToString() + "-" + fps_LD.ToString();     //标识物识别成功的帧率、光斑识别成功的帧率
                checkBox2.Checked = flags.LD_finded;                            //光斑识别结果标志
                checkBox3.Checked = flags.cover;                                //是否覆盖标志
                checkBox4.Checked = flags.goal_miss;                            //目标丢失标志
                checkBox5.Checked = flags.halo;                                 //光晕标志

                if(_tlCamera!= null)
                {
                    textBox8.Text = this._tlCamera.GetMeasuredFrameRate().ToString();   //相机采集图像实测帧率
                }
            }
        }

        private void button6_Click(object sender, EventArgs e)
        {//ROI全局设置，恢复默认的全部区域

            if(_latestProcessBitmap!=null)
            {
                lock(_lockableSharedData)
                {
                    try 
                    {
                        this._tlCamera.Disarm();
                        this._lockableSharedData.IsUpdateUIRequested = false;
                        this._lockableSharedData.LatestImageData = new ImageDataUShort1D(_processedImage, 1440, 1080, 10, ImageDataFormat.BGRPixel);
                        _latestProcessBitmap = null;
                        _tlCamera.ROIAndBin = new Thorlabs.TSI.TLCameraInterfaces.ROIAndBin() { ROIOriginX_pixels = 0, ROIOriginY_pixels = 0, ROIHeight_pixels = 1080, ROIWidth_pixels = 1440, BinX = bin, BinY = bin };
                        width = (int)_tlCamera.ROIAndBin.ROIWidth_pixels;
                        height = (int)_tlCamera.ROIAndBin.ROIHeight_pixels;
                        start_x = (int)_tlCamera.ROIAndBin.ROIOriginX_pixels;
                        start_y = (int)_tlCamera.ROIAndBin.ROIOriginY_pixels;
                        this._tlCamera.Arm();
                        //this._tlCamera.OnImageFrameAvailable += this.OnImageFrameAvailable;
                        this._tlCamera.IssueSoftwareTrigger();
                    }
                    catch(Exception)
                    {
                        MessageBox.Show("Set ROI OK.");
                    }
                }



            }
        }

        private void numericUpDown7_ValueChanged(object sender, EventArgs e)
        {//修改通信距离
            Distance = (double)numericUpDown7.Value;
        }

        private void numericUpDown8_ValueChanged(object sender, EventArgs e)
        {//修改振镜在相机坐标下的Z方向坐标
            Zm = (double)numericUpDown8.Value;
        }

        private void numericUpDown9_ValueChanged(object sender, EventArgs e)
        {//修改目标中心和接收中心的X方向位移偏移
            delt_X_c2c = (int)numericUpDown9.Value;                             //图像坐标系下偏差（int）
            Xc2center = -delt_X_c2c * pixel_size_x / Focal_length * Distance;   //世界坐标系下偏差（double）
        }

        private void numericUpDown10_ValueChanged(object sender, EventArgs e)
        {//修改目标中心和接收中心的Y方向位移偏移
            delt_Y_c2c = (int)numericUpDown10.Value;                            //图像坐标系下偏差（int）
            Yc2center = -delt_Y_c2c * pixel_size_y / Focal_length * Distance;   //世界坐标系下偏差（double）
        }

        private void numericUpDown11_ValueChanged(object sender, EventArgs e)
        {//修改振镜在相机坐标下的X方向坐标
            Xm = (double)numericUpDown11.Value;
        }

        private void numericUpDown12_ValueChanged(object sender, EventArgs e)
        {//修改振镜在相机坐标系下的Y方向坐标
            Ym = (double)numericUpDown12.Value;
        }

        private void checkBox6_CheckedChanged(object sender, EventArgs e)
        {//修改PID表示，表示是否启用PID控制
            flags.PID =  checkBox6.Checked;
        }

        private void numericUpDown13_ValueChanged(object sender, EventArgs e)
        {//修改卡尔曼滤波的测量误差
            for (int i = 0; i < num_kals; i++)
            {
               Kals.ElementAt(i).MeasurementNoiseCov.SetIdentity((float)numericUpDown13.Value);
            }
        }

        private void numericUpDown14_ValueChanged(object sender, EventArgs e)
        {//修改卡尔曼滤波器的预测误差
            for (int i = 0; i < num_kals; i++)
            {
                Kals.ElementAt(i).ProcessNoiseCov.SetIdentity((float)numericUpDown14.Value);
            }
        }

        private void checkBox8_CheckedChanged(object sender, EventArgs e)
        {//移动性能测试,移动测试状态下，默认不采用PID（延迟过高）
            flags.move_test = checkBox8.Checked;
            if (flags.move_test)
            {
                if (mirror_clock == null)           //移动测试状态下，振镜控制单独使用控制时钟进行轮询调用
                {
                    mirror_clock = new System.Timers.Timer(T_mirror);
                    mirror_clock.AutoReset = true;
                    mirror_clock.Enabled = true;
                    mirror_clock.Elapsed += new System.Timers.ElapsedEventHandler(mirror_control);
                }
                mirror_clock.Start();
                flags.PID = false;                  //禁用PID控制
                checkBox6.Checked = false;          //UI组件PID状态更新
                checkBox6.Enabled = false;          //禁止个人修改PID采用状态
            }
            else
            {                                       //恢复非移动测试状态时，PID及响应标志都恢复默认
                if (mirror_clock != null)
                    mirror_clock.Stop();
                flags.PID = true;
                checkBox6.Checked = true;
                checkBox6.Enabled = true;
            }
        }

        private void checkBox7_CheckedChanged(object sender, EventArgs e)
        {//修改kalman标志，表示是否启用卡尔曼滤波（预测）
            flags.kalman = checkBox7.Checked;
        }

        private void numericUpDown15_ValueChanged(object sender, EventArgs e)
        {//修改边缘修正左侧的X方向最大偏移
            added_bias[0] = (int)numericUpDown15.Value;
        }

        private void numericUpDown16_ValueChanged(object sender, EventArgs e)
        {//修改边缘修正右侧的X方向最大偏移
            added_bias[2] = (int)numericUpDown16.Value;
        }

        private void numericUpDown17_ValueChanged(object sender, EventArgs e)
        {//此函数是更改多卡尔曼滤波器的回调函数
            int new_num_kals = (int)numericUpDown17.Value;
            if (new_num_kals >= num_kals)
            {
                for (int i = num_kals; i < new_num_kals; i++)
                {
                    Kals.Add(Kals.ElementAt(0));
                }
            }
            else
            {
                for (int i = num_kals; i>new_num_kals;i--)
                {
                    Kals.RemoveAt(i-1);
                }
            }
            num_kals = new_num_kals;
        }

        private void button5_Click(object sender, EventArgs e)
        {//拍照按钮，存储当前帧图片
            if (_latestDisplayBitmap!=null)
            {
                send_test++;                                                                        //此参数用于标识当前保存的图片
                if (this._latestDisplayBitmap != null)
                {
                    string path = "D:\\文件\\图片保存\\" + send_test.ToString()+".jpg";
                    this._latestDisplayBitmap.Save(path, System.Drawing.Imaging.ImageFormat.Jpeg);
                }
            }
            else
            {
                MessageBox.Show("Please connect the camera first.");
            }


        }

        private void numericUpDown1_ValueChanged(object sender, EventArgs e)
        {//根据输入数值更改相机曝光时间
            if (this._tlCamera != null)
            {
                this.expose_time = (uint)numericUpDown1.Value;
                this._tlCamera.ExposureTime_us = (uint)numericUpDown1.Value;
            }
        }

        private void numericUpDown5_ValueChanged(object sender, EventArgs e)
        {//修改LD识别窗口尺寸
            win_LD = (int)numericUpDown5.Value;
        }

       
        private void numericUpDown6_ValueChanged(object sender, EventArgs e)
        {//覆盖判别的阈值设置
            cover_thre = (double)numericUpDown6.Value;
        }

        private void numericUpDown2_ValueChanged(object sender, EventArgs e)
        {//根据输入数值更改相机黑电平
            uint black_level = (uint)numericUpDown2.Value;
            if (this._tlCamera != null)
            {
                this._tlCamera.BlackLevel = black_level;
            }
        }

        private void numericUpDown3_ValueChanged(object sender, EventArgs e)
        {//根据输入数值更改X识别阈值
            this.win_center = (int)numericUpDown3.Value;
        }

        private void numericUpDown4_ValueChanged(object sender, EventArgs e)
        {//根据输入数值更改LD识别阈值，经验认定，在背景板设置合适情况下此值的可取范围广泛
            this.LD_thre = (double)numericUpDown4.Value;
        }

        private void button2_Click(object sender, EventArgs e)
        {//对准开始按钮
            if (_latestProcessBitmap != null)
            {
                flags.check = true;                                         //对准标志

                /*时钟控制振镜，此处用于修改振镜控制模式，若启用，同样需要修改的有①LD识别程序后的振镜控制、②重载的mirror_control()部分
                if(mirror_clock == null )
                {
                mirror_clock = new System.Timers.Timer(T_mirror);
                mirror_clock.AutoReset = true;
                mirror_clock.Enabled = true;
                mirror_clock.Elapsed += new System.Timers.ElapsedEventHandler(mirror_control);
                }
                */
                /*开始时钟记时,用于帧率计算*/
                if (fps_clock == null)
                {
                    fps_clock = new System.Timers.Timer(T_fps);
                    fps_clock.AutoReset = true;
                    fps_clock.Enabled = true;
                    fps_clock.Elapsed += new System.Timers.ElapsedEventHandler(fps_counter);
                    fps_clock.Start();
                }
            }
            else
            {
                MessageBox.Show("Please connect the camera first.");
            }
        }

        private void button7_Click(object sender, EventArgs e)
        {//ROI局部设置

                if (_latestProcessBitmap != null)
                {

                    Mat srcmat = OpenCvSharp.Extensions.BitmapConverter.ToMat(_latestProcessBitmap);

                    for (int i=0;  i < 10; i++)                                                 //为防止单次寻找失败，重复进行多次
                    {
                        int cal_x, cal_y;
                        getcircle(srcmat,true,out cal_x,out cal_y);                             //先全局寻找圆环，确定自动设置ROI中心区域
                        if(flags.X_finded)
                        {
                            this._tlCamera.Disarm();
                            uint roi_r0 = (uint)Math.Max(0, cal_y + height / 2 - r - 20);       //根据寻找标志结果进行设置ROI
                            uint roi_h = (uint)r * 2 + 40;
                            lock(_latestDisplayBitmap)
                            {
                                _tlCamera.ROIAndBin = new Thorlabs.TSI.TLCameraInterfaces.ROIAndBin() { ROIOriginX_pixels = 0, ROIOriginY_pixels = roi_r0, ROIHeight_pixels = roi_h, ROIWidth_pixels = 1440, BinX = bin, BinY = bin };
                                width = (int)_tlCamera.ROIAndBin.ROIWidth_pixels;
                                height = (int)_tlCamera.ROIAndBin.ROIHeight_pixels;
                                start_x = (int)_tlCamera.ROIAndBin.ROIOriginX_pixels;
                                start_y = (int)_tlCamera.ROIAndBin.ROIOriginY_pixels;
                                circles[0].Center.X = circles[0].Center.Y = 0;
                                this._tlCamera.Arm();
                                this._tlCamera.IssueSoftwareTrigger();
                            }
                            break;
                        }
                    }
                }
                else
                {
                    MessageBox.Show("Please connect the camera first.");
                }


        }
        public void getcircle(Mat srcmat, bool general, out int cal_x, out int cal_y)
        {
            Mat[] channels;
            Cv2.Split(srcmat, out channels);                                                                        //BGR 三色通道分离
            Mat red_mat = channels[2];                                                                              //采用红色通道矩阵用来识别光晕
            Mat circle_search_mat =  new Mat();                                                                     //圆形寻找区域
            Cv2.CvtColor(srcmat, circle_search_mat, ColorConversionCodes.BGR2GRAY);                                 //在灰度图上进行寻找圆环
            int base_c =0, base_r = 0;                                                                              //寻找区域的开始像素行列

            if (!general)                                                                                           //此处根据标志设置搜找范围，默认为全图
            {
                int range_search = 150;
                int[] search_area = new int[4] { Math.Max((int)circles[0].Center.X - range_search, 0),              //矩形区域的四角位置
                                                Math.Min((int)circles[0].Center.X + range_search, width), 
                                                Math.Max((int)circles[0].Center.Y - range_search, 0), 
                                                Math.Min((int)circles[0].Center.Y + range_search, height) };    
                base_c = search_area[0];
                base_r = search_area[2];
                circle_search_mat = new Mat(circle_search_mat,                                                      //对区域进行裁剪
                                            new OpenCvSharp.Range(search_area[2], search_area[3]),  
                                            new OpenCvSharp.Range(search_area[0], search_area[1])).Clone();
            }

            circles_temp = Cv2.HoughCircles(circle_search_mat, HoughModes.GradientAlt,                              //霍夫圆法找圆环，参数说明：输入图像，寻找方法
                                            2, 80, 200, 0.75,                                                       //分辨率降低倍数，圆环间最小距离，边缘检测高阈值，累加器阈值（<1,越大越圆）
                                            10/(int)bin, 20/(int)bin);                                             //最小半径，最大半径，

            if (circles_temp.Length == 1)                                                                           //当有且仅有一个圆环时，认定找到目标    
            {
                circles_temp.CopyTo(circles, 0);
                flags.X_finded = true;
                flags.goal_miss = false;                                                                            //目标丢失标志
                flags.halo = false;                                                                                 //受光晕影响丢失目标标志，用于受光晕影响情况下，振镜控制条件

                fail_counter = 0;                                                                                   //重置失败帧数
                checkBox1.Checked = true;                                                                           //UI界面指示目标未丢失
                circles[0].Center.X += base_c;                                                                      //中心在整张图片的行列
                circles[0].Center.Y += base_r;

                cal_x = (int)circles[0].Center.X - width / 2;                                                       //转成图像坐标系下坐标
                cal_y = (int)circles[0].Center.Y - height / 2;
                ++frame_counter_X;
            }
            else
            {
                cal_x = 0;
                cal_y = 0;
                flags.X_finded = false;                                                                 //当前帧寻找失败
                flags.goal_miss = general;                                                              //多次局部搜寻失败的情况下，认定寻找失败，开始全局寻找，并依旧失败，认定目标丢失
                checkBox1.Checked = !flags.goal_miss;                                                   //使用general赋值的情况下，在局部搜寻失败时，不认定目标丢失。
                fail_counter++;                                                                         //失败次数加一，超过一定数量，认定局部寻找失败，会进行全局寻找。
            }

            if (flags.goal_miss)                                                                        //判别目标丢失是否因为光晕
            {                                                                                           //此处方案较为简单，指定尺寸内红色高像素值比例大于某一阈值
                int center_x = center.X + width / 2;
                int center_y = center.Y + height / 2;
                int scan_width = 100, scan_height = 100;                                                //LD寻找范围，为矩形边长一半
                int start_c = Math.Max(center_x - scan_width, 0);
                int start_r = Math.Max(center_y - scan_height, 0);
                int stop_c = Math.Min(center_x + scan_width, width);
                int stop_r = Math.Min(center_y + scan_height, height);
                Mat part = new Mat(red_mat, new OpenCvSharp.Range(start_r, stop_r), new OpenCvSharp.Range(start_c, stop_c)).Clone();
                Mat bi_part_red = part.Threshold(150, 1, ThresholdTypes.Binary);                        //二值化，筛选高阈值
                Scalar sum_red = bi_part_red.Sum();
                if (sum_red[0] > bi_part_red.Height * bi_part_red.Width * 0.2)                          //此处指定尺寸内红色高像素值比例大于阈值(此处0.2)
                {
                    flags.halo = true;                                                                  //存在光晕
                }
            }
        }

        public void process_getLD(ref Mat srcmat)
        {
            get_LD(ref srcmat);                                                                         //寻找LD
            getActual_XY();                                                                             //转换得到圆环中心的世界坐标
            if (!flags.move_test)
                mirror_control();                                                                       //非移动测试状态下，控制振镜偏转
        }


        public void process_getX(ref Mat srcmat)
        {/*getcircle部分仅负责单次寻找圆环，对于寻找圆环的结果以及判断，由后续movejudge完成*/
            int cal_x, cal_y;
            bool general = (flags.X_finded || fail_counter < 3)? false : true;
            getcircle(srcmat, general, out cal_x, out cal_y);                                           //获取单次圆环寻找结果
            if (flags.X_finded)                                                                         //根据寻找结果以及当前模式对寻找结果进行处理
            {
                if (!flags.kalman)
                {
                    position_filter(cal_x, cal_y);                                                      //未采用卡尔曼，此处位置滤波主要作用是平均、添加边缘修正
                }
                else 
                {
                    position_filter_Kalman(cal_x, cal_y, frame_counter_X);                              //采用卡尔曼，此处位置滤波主要作用是以预测位置作为对准中心
                }
            }
        }

        public void get_LD(ref Mat srcmat)
        {
            if (flags.X_finded || flags.halo)//
            {
                Mat[] channels;
                Cv2.Split(srcmat, out channels);                                                //BGR 三色通道分离
                //Mat blue_mat = channels[1];
                Mat red_mat  = channels[2];
                //Mat connection = new Mat();                                                   //识别连通域
                System.Drawing.Point LD_center = new System.Drawing.Point(0,0);
                int num = 0;

                /*寻找LD图像区域*/
                int center_x = center.X + width / 2;                                            //依据目前的标识物中心
                int center_y = center.Y + height / 2;                                       
                int scan_width = r / 1, scan_height = r / 1;                                    //LD寻找范围
                int start_c = Math.Max(center_x - scan_width, 0);
                int start_r = Math.Max(center_y - scan_height, 0);
                int stop_c = Math.Min(center_x + scan_width, width);
                int stop_r = Math.Min(center_y + scan_height, height);

                //二值化并进行均值滤波，寻找最大点作为LD中心
                Mat part1 = new Mat(red_mat, new OpenCvSharp.Range(start_r, stop_r),            //裁剪红色通道
                                            new OpenCvSharp.Range(start_c, stop_c)).Clone();
                Mat bi_part = part1.Threshold(250, 255, ThresholdTypes.Binary);                 //根据阈值二值化，筛选高像素点
                 // Mat part1 = new Mat(bi_part, new OpenCvSharp.Range(start_r, stop_r), new OpenCvSharp.Range(start_c, stop_c)).Clone();
                Mat mean = bi_part.Blur(new OpenCvSharp.Size(win_LD, win_LD));                  //进行均值滤波，此处作用相当于滑动窗统计窗内高像素占比

                #region 识别连通域处理，暂时未用到8
                /*下面一部分注释，为识别连通域处理，暂时未用到*/
                //num = Cv2.ConnectedComponents(mean, connection, PixelConnectivity.Connectivity8, MatType.CV_16UC1);//这部分使用阈值处理后的图像，范围更小
                //LD_center = Get_connection_center(connection, mean, num);

                //Cv2.FindContours(mean,out contours, out hier, RetrievalModes.Tree, ContourApproximationModes.ApproxNone);
                //Cv2.DrawContours(part1,contours,-1,new Scalar(0,255,0),3);
                //part1.ImWrite("D:\\文件(desktop)\\清华\\研一\\oppo\\mat_save_gray\\contour2.jpg");
                #endregion

                double Max_rate, Min_rate;
                int[] max_idx = new int[2];                                                     //arr[0] 代表坐标y ，arr[1]代表坐标x
                int[] min_idx = new int[2];
                mean.MinMaxIdx(out Min_rate, out Max_rate, min_idx, max_idx);                   //获取最大值的坐标,衣次作为寻找结果

                LD.X = start_c + max_idx[1] - width / 2;                                        //获取寻找结果在整张图片的图像坐标
                LD.Y = start_r + max_idx[0] - height / 2;
                //LD.X = start_c + LD_center.X - width / 2;
                //LD.Y = start_r + LD_center.Y - height / 2;

                if (Max_rate > LD_thre * 255)                                                   //仅认定当比例高于阈值时，寻找成功
                {
                    flags.LD_finded = true;
                    ++frame_counter_LD;

                    //part2用于判别接收点是否被激光覆盖
                    Mat bi_part2 = part1.Threshold(250,255,ThresholdTypes.Binary);              //进行二值化
                    Mat part2 = new Mat(bi_part2, new OpenCvSharp.Range(Math.Max(center_y + delt_Y_c2c  - start_r - win_center, 0),         //裁剪覆盖区域的图像
                                                                        Math.Min(center_y + delt_Y_c2c - start_r + win_center, height)),
                                                    new OpenCvSharp.Range(Math.Max(center_x + delt_X_c2c - start_c - win_center, 0), 
                                                                Math.Min(center_x + delt_X_c2c - start_c + win_center, width))).Clone();
                    Scalar sum_part = part2.Sum();
                    flags.cover = sum_part[0] / (255 * (part2.Rows * part2.Cols)) > cover_thre;                                            //高于阈值认定已经覆盖              
                }
                else
                {
                    flags.LD_finded = false;
                }
            } 
        }

        #region 计算轮廓质心，但该方法速度慢，目前未被采用
        /*计算轮廓质心，但该方法速度慢，目前未被采用*/
        /*
        public System.Drawing.Point Get_connection_center(Mat label, Mat img_blur,int num)
        {
            int sum_max = 0;
            System.Drawing.Point LD_center = new System.Drawing.Point(0,0);
            for (int k = 1; k <= num; k++)
            {
                int sum_col = 0, sum_row = 0, sum_all = 0;
                for (int i = 0; i < label.Cols; i++)
                {
                    for (int j = 0; j < label.Rows; j++)
                    {
                        if (label.At<ushort>(j, i) == k)
                        {
                            sum_col += i * img_blur.At<ushort>(j, i);//加权平均
                            sum_row += j * img_blur.At<ushort>(j, i);//加权平均
                            sum_all += img_blur.At<ushort>(j, i);
                        }
                    }
                }
                if (sum_all > sum_max)
                {
                    sum_max = sum_all;
                    //num_selected = k;
                    LD_center = new System.Drawing.Point((int)(sum_col / (sum_all)), (int)(sum_row / (sum_all)));
                }
            }
            return LD_center;
        }
        */
        #endregion
        public void getActual_XY()
        {/*计算目标的中心位置世界坐标*/

            Xc = -(center.X + start_x + width / 2 - 1440 / 2) * pixel_size_x / Focal_length * Distance;
            Yc = -(center.Y + start_y + height/2 - 1080 /2 ) * pixel_size_y / Focal_length * Distance;
            Zc = Distance;
            textBox2.Text = Xc.ToString("0.00") + "," + Yc.ToString("0.00") + "," + Zc.ToString("0.00");
        }

        public void getAngle_mirror()
        {/*计算振镜对应角度*/
            double Xc_m = Xc + Xc2center - Xm;
            double Yc_m = Yc + Yc2center - Ym;
            double Zc_m = Zc + Zc2center - Zm;

            thelt2 = Math.PI / 4 - Math.Atan(Yc_m / Zc_m) / 2;
            thelt1 = Math.Atan(-Xc_m / (Math.Sqrt(Zc_m * Zc_m + Yc_m * Yc_m) + H_m12)) / 2 + Math.PI / 4;

        }

        

        public void sendData(double thelt_1, double thelt_2)
        {/*向振镜串口发送信号，输入为弧度值，*/
            float V1 = -(float)(thelt_1 / Math.PI * 180 - 45) * 2;
            float V2 = -(float)(thelt_2 / Math.PI * 180 - 45) * 2;
            //textBox6.Text = V1.ToString("0.00") + ","+V2.ToString("0.00");
            if (this.com != null && this.com.IsOpen)
            {
                string data_send = "Set " + V1.ToString("0.00") + "," + V2.ToString("0.00") + ";";
                this.com.WriteLine(data_send);
                flags.mirror_recieved = false;
            }
            else
            {
                MessageBox.Show("No Serial Port connected.");
            }
        }

        //串口接收消息处理
        private void OnDataReceived(object sender, SerialDataReceivedEventArgs e)
        {/*接收振镜控制返回信号并处理*/
            try
            {
                byte[] bytesRecvData = new byte[com.ReadBufferSize + 1];
                int icount = com.Read(bytesRecvData, 0, com.ReadBufferSize);

                string strRecvData = Encoding.ASCII.GetString(bytesRecvData);
                flags.mirror_recieved = true;
                //textBox4.Text = strRecvData;
            }
            catch (Exception ex)
            {
                MessageBox.Show(ex.ToString());
            }
        }


        //public void mirror_control(object sender, System.Timers.ElapsedEventArgs e)
        public void mirror_control()
        //public void mirror_control()
        {/*振镜控制函数，调用于光斑识别线程内，采用PID*/
            if (this.com != null && this.com.IsOpen)
            {
               
                if ((!flags.LD_finded||!flags.PID) && (flags.X_finded || flags.halo))
                //Math.Pow(Xc - xc_last,2)+ Math.Pow(Yc-yc_last,2)> 20 || 
                {
                    getAngle_mirror(); 
                    sendData(thelt1, thelt2);
                }
                else if (flags.LD_finded && (flags.X_finded || flags.halo))
                {   //若标志和光斑均识别成功，使用振镜坐标系下目标点（PD中心）与激光点（实测）偏差进行振镜角度调整
                    double XLD = -LD.X * pixel_size_x / Focal_length * Distance - Xm;
                    double YLD = -LD.Y * pixel_size_y / Focal_length * Distance - Ym;

                    double delt_x = XLD - (Xc + Xc2center - Xm);
                    double delt_y = YLD - (Yc + Yc2center - Ym);

                    //if ((XLD != xld_last || YLD != yld_last) && !flag_cover)
                    if (!flags.cover)//未覆盖
                    {
                        bool f_send = false;
                        if (Math.Abs(delt_x) > 0)
                        {
                            thelt1 += kp * delt_x - kd * (delt_x - delt_x1);//PID控制
                            //xld_last = XLD;
                            delt_x2 = delt_x1;
                            delt_x1 = delt_x;
                            f_send = true;
                        }
                        if (Math.Abs(delt_y) > 0)
                        {
                            thelt2 += kp * delt_y - kd * (delt_y - delt_y1);//PID控制
                            //yld_last = YLD;
                            delt_y2 = delt_y1;
                            delt_y1 = delt_y;
                            f_send = true;
                        }
                        if (f_send)
                        {//微调角度
                            sendData(thelt1, thelt2);
                        }
                     }
                    }
            }
        }

        public void mirror_control(object sender, System.Timers.ElapsedEventArgs e)
        //public void mirror_control()
        {/*重载振镜控制函数，用于定时控制，直接控制，不使用PID*/
            if (this.com != null && this.com.IsOpen)
            {
                if ((!flags.LD_finded || !flags.PID) && (flags.X_finded || flags.halo))
                {
                    getAngle_mirror();
                    sendData(thelt1, thelt2);
                }
            }
       }

        private void xml_reader()
        {
            //读取部分计算参数
            xmlDoc = new XmlDocument();
            xmlDoc.Load(("parameter.xml"));
            XmlNode root = xmlDoc.DocumentElement;
            nodeList = xmlDoc.SelectSingleNode("parameters").ChildNodes;
            Xm = Convert.ToDouble(((XmlElement)nodeList[0]).GetAttribute("value"));
            Ym = Convert.ToDouble(((XmlElement)nodeList[1]).GetAttribute("value"));
            Xc2center = Convert.ToDouble(((XmlElement)nodeList[2]).GetAttribute("value"));
            Yc2center = Convert.ToDouble(((XmlElement)nodeList[3]).GetAttribute("value"));
            win_center = Convert.ToInt32(((XmlElement)nodeList[4]).GetAttribute("value"));
            win_LD = Convert.ToInt32(((XmlElement)nodeList[5]).GetAttribute("value"));
            // win_LD_width = Convert.ToInt32(((XmlElement)nodeList[5]).GetAttribute("value"));
            cover_thre = Convert.ToDouble(((XmlElement)nodeList[6]).GetAttribute("value"));
            delt_X_c2c = Convert.ToInt32(((XmlElement)nodeList[7]).GetAttribute("value"));
            delt_Y_c2c = Convert.ToInt32(((XmlElement)nodeList[8]).GetAttribute("value"));
            expose_time = Convert.ToUInt32(((XmlElement)nodeList[9]).GetAttribute("value"));
            Distance = Convert.ToDouble(((XmlElement)nodeList[10]).GetAttribute("value"));
            Zm = Convert.ToDouble(((XmlElement)nodeList[11]).GetAttribute("value"));
            num_kals = Convert.ToInt32(((XmlElement)nodeList[12]).GetAttribute("value"));

            foreach ( XmlNode node in root.ChildNodes)
            {
                if(node.Attributes["value"].Value.Equals("bias"))
                {
                    XmlNodeList nlt2 = node.ChildNodes;
                    for (int i=0; i<node.ChildNodes.Count; i++)
                    {
                        added_bias[i] = Convert.ToInt32(nlt2[i].InnerText);
                    }
                }
            }
        }

        private void xml_writer()
        {
            //保存参数
            ((XmlElement)nodeList[0]).SetAttribute("value", Xm.ToString());
            ((XmlElement)nodeList[1]).SetAttribute("value", Ym.ToString());
            ((XmlElement)nodeList[2]).SetAttribute("value", Xc2center.ToString());
            ((XmlElement)nodeList[3]).SetAttribute("value", Yc2center.ToString());
            ((XmlElement)nodeList[4]).SetAttribute("value", win_center.ToString());
            ((XmlElement)nodeList[5]).SetAttribute("value", win_LD.ToString());
            ((XmlElement)nodeList[6]).SetAttribute("value", cover_thre.ToString());
            ((XmlElement)nodeList[7]).SetAttribute("value", delt_X_c2c.ToString());
            ((XmlElement)nodeList[8]).SetAttribute("value", delt_Y_c2c.ToString());
            ((XmlElement)nodeList[9]).SetAttribute("value", expose_time.ToString());
            ((XmlElement)nodeList[10]).SetAttribute("value", Distance.ToString());
            ((XmlElement)nodeList[11]).SetAttribute("value", Zm.ToString());
            ((XmlElement)nodeList[12]).SetAttribute("value", num_kals.ToString());

            //保存参数，用于边缘修正的附加位移值
            foreach (XmlNode node in xmlDoc.DocumentElement.ChildNodes)
            {
                if (node.Attributes["value"].Value.Equals("bias"))
                {
                    XmlNodeList nlt2 = node.ChildNodes;
                    for (int i = 0; i < node.ChildNodes.Count; i++)
                    {
                        nlt2[i].InnerText = added_bias[i].ToString();
                    }
                }
            }

            xmlDoc.Save("parameter.xml");
        }

        /*识别后，对结果进行处理，平均、运动判别*/
        private void position_filter(int cal_x, int cal_y)
        {
            if (Math.Pow(cal_x - center.X, 2) + Math.Pow(cal_y - center.Y, 2) < 150)            //若偏差不大，认为接收机未移动，更新队列，对寻得中心点进行平均
            {
                if (Q_center.Count > 20)
                {
                    Q_center.Dequeue();
                }
                move_counter--;
            }
            else
            {                                                                                   //否则，认为已移动，重新填充队列
                Q_center.Clear();
                move_counter++;
            }

            //依据move_counter判别状态,on_move限制在0-5之间，在静止状态下，on_move增加到3，判为true，
            //移动状态下，on_move减至0判为false
            move_counter = move_counter < 0 ? 0 : move_counter;
            move_counter = move_counter > 5 ? 5 : move_counter;
            flags.on_move = move_counter == 3 && !flags.on_move ? true : flags.on_move;
            flags.on_move = move_counter == 0 && flags.on_move ? false : flags.on_move;

            Q_center.Enqueue(new OpenCvSharp.Point(cal_x, cal_y));

            cal_x = 0;
            cal_y = 0;
            OpenCvSharp.Point[] Arr_center = Q_center.ToArray();
            for (int i = 0; i < Q_center.Count; i++)
            {
                cal_x += Arr_center[i].X;
                cal_y += Arr_center[i].Y;
            }
            
            center.X = cal_x / Q_center.Count;                                                  //以队列均值作为目标中心
            center.Y = cal_y / Q_center.Count;
            //对识别结果进行边缘修正，采用简单的线性补偿
            if (center.X < - width / 2 + 150)
            {
                center.X += (150 - width / 2 - center.X) * added_bias[0] / 150;
                center.X = Math.Max(center.X, -width / 2);
            }
            else if (center.X > width / 2 - 150)
            { 
                center.X += (center.X - width / 2 + 150) * added_bias[2] / 150;
                center.X = Math.Min(center.X, width);
            }


            r = (int)circles_temp[0].Radius;
        }

        /*识别后，坐标处理，卡尔曼滤波，预测以及修正*/
        private void position_filter_Kalman(int cal_x, int cal_y, int frame)
        {
            int order_kal = frame % num_kals;
            //last_measurement = current_measurement.Clone();
            //last_prediction = current_prediction.Clone();

            current_measurement.At<float>(0) = (float)cal_x;
            current_measurement.At<float>(1) = (float)cal_y;
            //current_measurement.At<float>(2) = x_speed;
            //current_measurement.At<float>(3) = y_speed;
            Console.WriteLine(current_measurement.At<float>(0) + "," + current_measurement.At<float>(1));

            //Mat gain = kalmanfilter.Gain;//卡尔曼增益，用于调试程序时查看

            Mat state_corr = Kals.ElementAt(order_kal).Correct(current_measurement);//根据当前时刻测量值对上一时刻预测值进行修正，得出状态估计值
            //center.X = (int)state_corr.At<float>(0); center.Y = (int)state_corr.At<float>(1);
            //move_judge(cal_x,cal_y);

            //计算上一时刻预测偏差，采用欧氏距离
            //err = (float)Math.Sqrt(Math.Pow(((float)cal_x - last_prediction.At<float>(0)), 2) + Math.Pow(((float)cal_y - last_prediction.At<float>(1)), 2));
            //err_list.Add(err);
            //Console.WriteLine("当前测量值" + current_measurement.At<float>(0) + "," + current_measurement.At<float>(1));
            //Console.WriteLine("当前状态" + state_corr.At<float>(0) + "," + state_corr.At<float>(1));
            //Console.WriteLine("预测误差（欧氏距离）:" + err);

            current_prediction = Kals.ElementAt(order_kal).Predict();//预测

            //Console.WriteLine("外部控制量" + B.At<float>(0) + "," + B.At<float>(1));
            Console.WriteLine("");
            Console.WriteLine("下一时刻预测值" + current_prediction.At<float>(0) + "," + current_prediction.At<float>(1));

            //将预测值作为振镜目标位置
            center.X = (int)current_prediction.At<float>(0);
            center.Y = (int)current_prediction.At<float>(1);
            r = (int)circles_temp[0].Radius;

            /*存储当前卡尔曼滤波的估计、测量、预测结果,若需要，此函数需要传入图像矩阵，尚未修改*/
            //Cv2.DrawMarker(mat_tri, new OpenCvSharp.Point(center.X + width / 2, center.Y + height / 2), new Scalar(255, 0, 0));//当前状态估计值
            //Cv2.DrawMarker(mat_tri, new OpenCvSharp.Point(cal_x + width / 2, cal_y + height / 2), new Scalar(0, 255, 0), MarkerTypes.Diamond, 6);//当前状态测量值
            //Cv2.DrawMarker(mat_tri, new OpenCvSharp.Point(prediction.X + width / 2, prediction.Y + height / 2), new Scalar(0, 0, 255), MarkerTypes.TiltedCross);//下一状态预测值
            //Cv2.ImWrite("D:\\Code\\VS_program\\C#\\self_test_1_camera\\self_test_1_camera\\self_test_1_camera\\kalman_pre\\" + frame_counter_X.ToString() + ".jpg", mat_tri);

        }

        /*kalmanfiter初始化*/
        public void kalman_init()
        {
            //kalmanfilter = new OpenCvSharp.KalmanFilter(state_num, 2);

            last_measurement = new Mat(2, 1, MatType.CV_32FC1);//上一时刻测量值
            current_measurement = new Mat(2, 1, MatType.CV_32FC1);//当前时刻测量值
            last_prediction = new Mat(state_num, 1, MatType.CV_32FC1);//上一时刻预测值
            current_prediction = new Mat(state_num, 1, MatType.CV_32FC1);//当前时刻预测值
            //frame = new Mat(4,1, MatType.CV_8UC3);

            //A-预测矩阵，H-测量矩阵，p-预测误差矩阵，m-测量误差矩阵
            Mat A = new Mat(state_num, state_num, MatType.CV_32FC1, new float[16] { 1, 0, 1, 0, 0, 1, 0, 1, 0, 0, 1, 0, 0, 0, 0, 1 });
            Mat H = new Mat(2, state_num, MatType.CV_32FC1);//, new float[16] { 1, 0, 0, 0, 0, 1, 0, 0, 0, 0, 1, 0, 0, 0, 0, 1 });
            Mat p = new Mat(state_num, state_num, MatType.CV_32FC1);
            Mat m = new Mat(2, 2, MatType.CV_32FC1);//,new float[16] { 50, 0, 2f, 0, 0, 50, 0, 2f, 0, 0, 3f, 0, 0, 0, 0, 3f });

            //A.SetIdentity(1);
            H.SetIdentity(1);
            p.SetIdentity(100);
            m.SetIdentity(100);

            //kalmanfilter = new OpenCvSharp.KalmanFilter(state_num, 2);
            //kalmanfilter.TransitionMatrix = A;
            //kalmanfilter.MeasurementMatrix = H;
            //kalmanfilter.ProcessNoiseCov = p;
            //kalmanfilter.MeasurementNoiseCov = m;


            Kals = new List<KalmanFilter>(num_kals);
            for (int i = 0; i < num_kals; i++)
            {
                Kals.Add(new OpenCvSharp.KalmanFilter(state_num, 2));
                Kals.ElementAt(i).TransitionMatrix = A;
                Kals.ElementAt(i).MeasurementMatrix = H;
                Kals.ElementAt(i).ProcessNoiseCov = p;
                Kals.ElementAt(i).MeasurementNoiseCov = m;
            }
        }


        /*该函数 用于计算每秒识别成功的帧数*/
        public void fps_counter(object sender, System.Timers.ElapsedEventArgs e)
        {
            fps_X = frame_counter_X - frame_X_last;
            fps_LD = frame_counter_LD - frame_LD_last;
            frame_X_last = frame_counter_X;
            frame_LD_last = frame_counter_LD;
        }
    }
}
