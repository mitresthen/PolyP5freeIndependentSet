package no.uib.ii.algo.st8;

import java.io.BufferedReader;
import java.io.FileInputStream;
import java.io.FileNotFoundException;
import java.io.FileOutputStream;
import java.io.IOException;
import java.io.InputStreamReader;
import java.io.OutputStreamWriter;
import java.util.Date;
import java.util.List;

import no.uib.ii.algo.st8.algorithms.GraphInformation;
import no.uib.ii.algo.st8.interval.IntervalGraph;
import no.uib.ii.algo.st8.interval.SimpleToBasicWrapper;
import no.uib.ii.algo.st8.model.DefaultEdge;
import no.uib.ii.algo.st8.model.DefaultVertex;
import no.uib.ii.algo.st8.util.FileAccess;
import no.uib.ii.algo.st8.util.GraphExporter;

import org.json.JSONException;

import android.annotation.SuppressLint;
import android.app.Activity;
import android.app.AlertDialog;
import android.content.DialogInterface;
import android.content.Intent;
import android.graphics.Bitmap;
import android.graphics.BitmapFactory;
import android.graphics.Shader;
import android.graphics.drawable.BitmapDrawable;
import android.hardware.Sensor;
import android.hardware.SensorEvent;
import android.hardware.SensorEventListener;
import android.hardware.SensorManager;
import android.os.Bundle;
import android.text.ClipboardManager;
import android.text.Editable;
import android.util.DisplayMetrics;
import android.view.Menu;
import android.view.MenuInflater;
import android.view.MenuItem;
import android.view.View;
import android.view.View.OnClickListener;
import android.widget.EditText;
import android.widget.Toast;

/**
 * @author pgd
 */
public class Workspace extends Activity implements OnClickListener, SensorEventListener {

  @Override
  public void onBackPressed() {
    if (!controller.undo())
      super.onBackPressed();
  }

  private GraphViewController controller;

  private volatile boolean saveOnExit = false;

  /** Called when the activity is first created. */
  @Override
  public void onCreate(Bundle savedInstanceState) {
    super.onCreate(savedInstanceState);

    System.out.println("done markus log hei stupedamen");

    DisplayMetrics displaymetrics = new DisplayMetrics();
    getWindowManager().getDefaultDisplay().getMetrics(displaymetrics);
    int height = displaymetrics.heightPixels;
    int width = displaymetrics.widthPixels;

    // scaleGestureDetector = new ScaleGestureDetector(this,
    // new SimpleScaleGestureDetector());

    // Bitmapbmp=BitmapFactory.decodeResource(getResources(),R.drawable.bg_image);

    Bitmap bmp = BitmapFactory.decodeResource(getResources(), R.drawable.bg_image_larger);

    BitmapDrawable bitmapDrawable = new BitmapDrawable(bmp);
    bitmapDrawable.setTileModeXY(Shader.TileMode.REPEAT, Shader.TileMode.REPEAT);
    controller = new GraphViewController(this, width, height);
    controller.getView().setBackgroundDrawable(bitmapDrawable);

    setContentView(controller.getView());

    // shake
    sensorManager = (SensorManager) getSystemService(SENSOR_SERVICE);
    this.sensors = sensorManager.getSensorList(Sensor.TYPE_ACCELEROMETER);
    if (sensors.size() > 0) {
      sensor = sensors.get(0);
      sensorManager.registerListener(this, sensor, SensorManager.SENSOR_DELAY_GAME);
      System.out.println("PAAL REGISTERED SENSOR");
    }
    GraphViewController.EDGE_DRAW_MODE = false;

    String title = "Grapher";
    String message = "Tap to create vertices." + "\nHold to toggle between vertex creation and edge drawing mode.";

    AlertDialog.Builder builder = new AlertDialog.Builder(this);
    builder.setMessage(message).setTitle(title);

    builder.setPositiveButton("Ok!", new DialogInterface.OnClickListener() {
      @Override
      public void onClick(DialogInterface dialog, int which) {
        shortToast("Go ahead and graph!");
      }
    });
    builder.setNeutralButton("Load", new DialogInterface.OnClickListener() {
      @Override
      public void onClick(DialogInterface dialog, int which) {
        load();
      }
    });

    AlertDialog dialog = builder.create();
    dialog.show();
  }

  private boolean copyTikzToClipboard() {
    String text = GraphExporter.getTikz(controller.getGraph(), controller.getTransformMatrix());
    try {
      ClipboardManager clipboard = (ClipboardManager) getSystemService(CLIPBOARD_SERVICE);
      clipboard.setText(text);
      return true;
    } catch (Exception e) {
      System.err.println("Error while copying TiKZ to clipboard: " + e.getMessage());
      e.printStackTrace();
      e.printStackTrace();
      return false;
    }
  }

  private boolean copyMetapostToClipboard() {
    String text = GraphExporter.getMetapost(controller.getGraph());
    try {
      ClipboardManager clipboard = (ClipboardManager) getSystemService(CLIPBOARD_SERVICE);
      clipboard.setText(text);
      return true;
    } catch (Exception e) {
      System.err.println("Error while copying metapost to clipboard: " + e.getMessage());
      e.printStackTrace();
      return false;
    }
  }

  private SensorManager sensorManager;
  private List<Sensor> sensors;
  private Sensor sensor;
  private long lastUpdate = -1;
  private long currentTime = -1;

  private float last_x, last_y, last_z;
  private float current_x, current_y, current_z, currenForce;
  private static final int FORCE_THRESHOLD = 800; // used to be 900
  private final int DATA_X = SensorManager.DATA_X;
  private final int DATA_Y = SensorManager.DATA_Y;
  private final int DATA_Z = SensorManager.DATA_Z;

  // //// shake
  public void onAccuracyChanged(Sensor arg0, int arg1) {
  }

  public void onSensorChanged(SensorEvent event) {
    if (event.sensor.getType() != Sensor.TYPE_ACCELEROMETER || event.values.length < 3)
      return;

    currentTime = System.currentTimeMillis();

    if ((currentTime - lastUpdate) > 100) {
      long diffTime = (currentTime - lastUpdate);
      lastUpdate = currentTime;

      current_x = event.values[DATA_X];
      current_y = event.values[DATA_Y];
      current_z = event.values[DATA_Z];

      currenForce = Math.abs(current_x + current_y + current_z - last_x - last_y - last_z) / diffTime * 10000;

      if (currenForce > FORCE_THRESHOLD) {
        controller.shake();
      }

      last_x = current_x;
      last_y = current_y;
      last_z = current_z;

    }
  }

  private void shareTikz() {

    String shareBody = GraphExporter.getTikz(controller.getGraph(), controller.getTransformMatrix());

    Intent sharingIntent = new Intent(android.content.Intent.ACTION_SEND);
    sharingIntent.setType("text/plain");
    sharingIntent.putExtra(android.content.Intent.EXTRA_SUBJECT, controller.graphInfo());
    sharingIntent.putExtra(android.content.Intent.EXTRA_TEXT, shareBody);
    startActivity(Intent.createChooser(sharingIntent, "Share graph with"));

  }

  private boolean shareInterval() {
    String shareBody = "\\documentclass{article}\n\\usepackage{tikz}\n\\begin{document}\n\n";

    SimpleToBasicWrapper<DefaultVertex, DefaultEdge<DefaultVertex>> wrap = new SimpleToBasicWrapper<DefaultVertex, DefaultEdge<DefaultVertex>>(
        controller.getGraph());

    IntervalGraph ig = wrap.getIntervalGraph();
    if (ig == null)
      return false;

    shareBody += "\\begin{figure}[htp]";
    shareBody += "\\centering";

    shareBody += GraphExporter.getTikzIntervalRepresentation(wrap.getIntervalGraph());

    shareBody += "\n\t\\caption{" + GraphInformation.graphInfo(controller.getGraph()) + " (Grapher)}";
    shareBody += "\n\t\\label{fig:interval}";
    shareBody += "\n\t\\end{figure}";

    shareBody += "\n\n\\end{document}\n";

    Intent sharingIntent = new Intent(android.content.Intent.ACTION_SEND);
    sharingIntent.setType("text/plain");
    sharingIntent.putExtra(android.content.Intent.EXTRA_SUBJECT, controller.graphInfo());
    sharingIntent.putExtra(android.content.Intent.EXTRA_TEXT, shareBody);
    startActivity(Intent.createChooser(sharingIntent, "Share graph with"));

    return true;
  }

  private void shareMetapost() {
    String shareBody = GraphExporter.getMetapost(controller.getGraph());

    shareBody += "\n\n% Sent to you by Grapher";

    Intent sharingIntent = new Intent(android.content.Intent.ACTION_SEND);
    sharingIntent.setType("text/plain");
    sharingIntent.putExtra(android.content.Intent.EXTRA_SUBJECT, controller.graphInfo());
    sharingIntent.putExtra(android.content.Intent.EXTRA_TEXT, shareBody);
    startActivity(Intent.createChooser(sharingIntent, "Share graph with"));

  }

  // //// shake

  public void onClick(View v) {
    // ignoring clicks, listens to gesture stuff anyway
  }

  // Initiating Menu XML file (menu.xml)
  public boolean onCreateOptionsMenu(Menu menu) {
    MenuInflater menuInflater = getMenuInflater();
    menuInflater.inflate(R.layout.drawer_context, menu);
    return true;
  }

  /**
   * returns a string containing date and graph info
   */
  private String createFileName() {
    return new Date().toGMTString() + " " + controller.graphInfo();
  }

  @Override
  @SuppressLint("WorldReadableFiles")
  protected void onDestroy() {
    super.onDestroy();

    if (controller.getGraph().vertexSet().size() > 0 && saveOnExit) {
      try {
        String json = new FileAccess().save(controller.getGraph());
        FileOutputStream fOut = openFileOutput(createFileName() + ".json", MODE_WORLD_READABLE);
        OutputStreamWriter osw = new OutputStreamWriter(fOut);

        // Write the string to the file
        osw.write(json);

        /*
         * ensure that everything is really written out and close
         */
        osw.flush();
        osw.close();

      } catch (JSONException e) {
        e.printStackTrace();
      } catch (IOException e) {
        e.printStackTrace();
      }
    }
    // Unregister from SensorManager.
    sensorManager.unregisterListener(this);
    sensorManager.unregisterListener(this, sensor);
    for (Sensor s : sensors) {
      sensorManager.unregisterListener(this, s);
    }
  }

  public void longToast(String toast) {
    Toast.makeText(Workspace.this, toast, Toast.LENGTH_LONG).show();
  }

  public void shortToast(String toast) {
    Toast.makeText(Workspace.this, toast, Toast.LENGTH_SHORT).show();
  }

  /**
   * Event Handling for Individual menu item selected Identify single menu item
   * by it's id
   * */
  public boolean onOptionsItemSelected(MenuItem item) {
    // System.out.println("MenuItem      \t" + item.getTitle());
    // System.out.println(" > Condensed  \t" + item.getTitleCondensed());
    // System.out.println(" > numeric id \t" + item.getItemId());
    // System.out.println();

    switch (item.getItemId()) {

    case R.id.finish:
      saveOnExit = false;
      finish();
      return true;

    case R.id.finish_and_save:
      saveOnExit = true;
      finish();
      return true;

    case R.id.new_graph:
      controller.newGraph();
      return true;

    case R.id.snap:
      controller.snapToGrid();
      return true;

      // case R.id.chordalization:
      // controller.showChordalization();
      // return true;

    case R.id.threshold:
      controller.showThreshold();
      return true;

    case R.id.compute_maximum_independent_set:
      controller.showMaximumIndependentSet();
      return true;

    case R.id.compute_chromatic_number:
      controller.chromaticNumber();
      return true;

    case R.id.compute_colouring:
      controller.showColouring();
      return true;

    case R.id.compute_maximum_clique:
      controller.showMaximumClique();
      return true;

    case R.id.vertex_integrity:
      controller.showVertexIntegrity();
      return true;

    case R.id.compute_minimal_triangulation:
      controller.minimalTriangulation();
      return true;

    case R.id.compute_steiner_tree:
      controller.showSteinerTree();
      return true;

    case R.id.clear_colours:
      controller.clearAll();
      return true;

    case R.id.compute_treewidth:
      controller.treewidth();
      return true;

    case R.id.compute_simplicial_vertices:
      int simplicials = controller.showSimplicialVertices();
      if (simplicials > 1)
        shortToast(simplicials + " simplicial vertices");
      else if (simplicials == 1)
        shortToast(simplicials + " simplicial vertex");
      else
        shortToast("No simplicial vertices.");
      return true;

    case R.id.compute_chordality:
      boolean isChordal = controller.isChordal();
      if (isChordal)
        shortToast("Graph is chordal.");
      else
        shortToast("Graph is not chordal.");
      return true;

    case R.id.compute_claw_deletion:
      int deletionSize = controller.showClawDeletion();
      if (deletionSize == 0)
        shortToast("Graph is claw-free");
      else
        shortToast("Claw-free deletion size " + deletionSize);
      return true;

    case R.id.compute_perfect_code:
      controller.showPerfectCode();
      return true;

    case R.id.compute_claws:
      boolean hasclaw = controller.showAllClaws();
      if (hasclaw)
        shortToast("Found claw");
      else
        shortToast("Graph is claw-free");
      return true;

    case R.id.compute_cycle_4:
      controller.showAllCycle4();
      return true;

    case R.id.compute_regularity_deletion_set:
      controller.showRegularityDeletionSet();
      return true;

    case R.id.compute_odd_cycle_transversal:
      controller.showOddCycleTransversal();
      return true;

    case R.id.compute_feedback_vertex_set:
      controller.showFeedbackVertexSet();
      return true;

    case R.id.compute_connected_feedback_vertex_set:
      controller.showConnectedFeedbackVertexSet();
      return true;

    case R.id.compute_vertex_cover:
      controller.showVertexCover();
      return true;

    case R.id.compute_connected_vertex_cover:
      controller.showConnectedVertexCover();
      return true;

    case R.id.compute_minimum_dominating_set:
      controller.showDominatingSet();
      return true;

      // case R.id.compute_minimum_red_blue_dominating_set:
      // controller.showRedBlueDominatingSet();
      // return true;

    case R.id.spring:
      controller.longShake(300);
      shortToast("Shaken, not stirred");
      return true;

    case R.id.hamiltonian_path:
      controller.showHamiltonianPath();
      return true;

    case R.id.hamiltonian_cycle:
      controller.showHamiltonianCycle();
      return true;

    case R.id.flow:
      int flow = controller.showFlow();
      if (flow < 0)
        shortToast("Please select two vertices (hold to select)");
      else if (flow == 0)
        shortToast("Not connected");
      else
        shortToast("Max flow " + flow);
      return true;

    case R.id.path:
      int res = controller.showPath();
      if (res < 0)
        shortToast("Please select two vertices (hold to select)");
      else if (res == 0)
        shortToast("No path!");
      else
        shortToast("Path length " + res);
      return true;

    case R.id.power:
      controller.constructPower();
      shortToast("Power graph has been constructed");
      return true;

    case R.id.compute_mst:
      controller.showSpanningTree();
      return true;

    case R.id.compute_balanced_separator:
      controller.showSeparator();
      return true;

    case R.id.compute_diameter:
      int diam = controller.diameter();
      if (diam < 0)
        shortToast("Diameter is infinite");
      else
        shortToast("Diameter " + diam);

      return true;

    case R.id.compute_girth:
      int girth = controller.girth();
      if (girth < 0)
        shortToast("Acyclic");
      else
        shortToast("Girth " + girth);

      return true;

    case R.id.bipartition:
      boolean bipartite = controller.showBipartition();
      if (bipartite)
        shortToast("Is bipartite");
      else
        shortToast("Is not bipartite");
      return true;

    case R.id.compute_all_cuts:
      int cuts = controller.showAllCutVertices();
      if (cuts == 0)
        shortToast("No cut vertices");

      else if (cuts == 1)
        shortToast("1 cut vertex");
      else
        shortToast(cuts + " cut vertices");
      return true;

    case R.id.compute_all_bridges:
      int bridges = controller.showAllBridges();
      if (bridges == 0)
        shortToast("No bridges");
      else if (bridges == 1)
        shortToast("1 bridge");
      else
        shortToast(bridges + " bridges");
      return true;

    case R.id.test_eulerian:
      boolean eulerian = controller.isEulerian();
      if (eulerian)
        shortToast("Graph is eulerian");
      else
        shortToast("Graph is not eulerian, odd degree vertices highlighted.");
      return true;

    case R.id.show_center:
      boolean conn = controller.showCenterVertex();
      if (!conn)
        shortToast("No center vertex in disconnected graph");
      return true;

    case R.id.centralize:
      controller.centralize();
      return true;

    case R.id.add_universal_vertex:
      int degree = controller.addUniversalVertex();
      if (degree == 0)
        shortToast("Added singleton");
      else if (degree == 1)
        shortToast("Added vertex adjacent to 1 vertex");
      else
        shortToast("Added vertex adjacent to " + degree + " vertices");
      return true;

    case R.id.compute_bandwidth:
      controller.computeBandwidth();
      return true;

    case R.id.metapost_to_clipboard:
      if (copyMetapostToClipboard()) {
        shortToast("Copied info on " + controller.graphInfo());
      } else {
        shortToast("An error occured copying to clipboard!");
      }
      return true;

    case R.id.tikz_to_clipboard:
      if (copyTikzToClipboard()) {
        shortToast("Copied info on " + controller.graphInfo());
      } else {
        shortToast("An error occured copying to clipboard!");
      }
      return true;

    case R.id.share_tikz:
      shareTikz();
      return true;

    case R.id.share_interval:
      if (shareInterval()) {
        return true;
      }

      // DO NOT PUT ANYTHING HERE!

      // THE CASE ABOVE DOES NOT BREAK IF GRAPH NOT INTERVAL

    case R.id.interval:
      int interval = controller.showInterval();
      switch (interval) {
      case 0:
        shortToast("Graph is interval");
        break;
      case 1:
        shortToast("Not interval, AT is highlighted");
        break;
      case 2:
        shortToast("Not chordal");
      }
      return true;

      // TODO SCREENSHOT SAVING MUST SAVE IN EXTERNAL
      // case R.id.screenshot:
      // if (!writeScreenshot()) {
      // longToast("Writing failed.");
      // }
      // return true;

    case R.id.share_metapost:
      shareMetapost();
      return true;

    case R.id.select_all:
      controller.selectAll();
      return true;

    case R.id.deselect_all:
      controller.deselectAll();
      return true;

    case R.id.select_all_highlighted_vertices:
      controller.selectAllHighlightedVertices();
      return true;

    case R.id.invert_selected:
      controller.invertSelectedVertices();
      return true;

    case R.id.select_reachable:
      controller.selectAllReachableVertices();
      return true;


    case R.id.local_complement:
      if (!controller.localComplement()) {
        shortToast("Select at least one vertex to perform local complement");
      }
      return true;

    case R.id.contract:
      if (!controller.contract()) {
        shortToast("Select two adjacent vertices");
      }
      return true;

    case R.id.complete_selected:
      controller.completeSelectedVertices();
      return true;

    case R.id.complement_selected:
      controller.complementSelected();
      return true;

    case R.id.delete_selected:
      int deleted = controller.deleteSelectedVertices();
      if (deleted == 0) {
        shortToast("No vertices selected");
      } else {
        shortToast("Deleted " + deleted + " vertices");
      }
      return true;

    case R.id.induce_subgraph:
      int removed = controller.induceSubgraph();
      if (removed == 0) {
        shortToast("All vertices selected, none deleted");
      } else {
        shortToast("Removed " + removed + " vertices");
      }
      return true;

    case R.id.toggle_edge_edit:
      boolean edgedraw = controller.toggleEdgeDraw();
      shortToast(edgedraw ? "Edge draw mode" : "Vertex move mode");
      return true;

    case R.id.save:
      save();
      return true;

    case R.id.load:
      load();
      return true;

    case R.id.delete:
      delete();
      return true;

    case R.id.toggle_label_drawing:
      boolean doShow = !GraphViewController.DO_SHOW_LABELS;
      GraphViewController.DO_SHOW_LABELS = doShow;
      if (doShow)
        shortToast("Showing labels");
      else
        shortToast("Not showing labels");
      controller.redraw();
      return true;

    default:
      System.out.println("Option item selected, " + item.getTitle());
      return super.onOptionsItemSelected(item);
    }
  }

  public void save() {

    System.out.println("save");
    AlertDialog.Builder alert = new AlertDialog.Builder(this);

    alert.setTitle("Title");
    alert.setMessage("Message");

    // Set an EditText view to get user input
    final EditText input = new EditText(this);
    alert.setView(input);

    alert.setPositiveButton("Ok", new DialogInterface.OnClickListener() {
      @SuppressLint("WorldReadableFiles")
      public void onClick(DialogInterface dialog, int whichButton) {
        Editable value = input.getText();
        try {
          String json = new FileAccess().save(controller.getGraph());
          FileOutputStream fOut = openFileOutput(value + ".json", MODE_WORLD_READABLE);
          OutputStreamWriter osw = new OutputStreamWriter(fOut);

          // Write the string to the file
          osw.write(json);

          /*
           * ensure that everything is really written out and close
           */
          osw.flush();
          osw.close();

        } catch (JSONException e) {
          e.printStackTrace();
        } catch (IOException e) {
          e.printStackTrace();
        }
      }
    });

    alert.setNegativeButton("Cancel", new DialogInterface.OnClickListener() {
      public void onClick(DialogInterface dialog, int whichButton) {
        // Canceled.
      }
    });

    alert.show();
  }

  /**
   * Write a screenshot to file, calls first controller.screenshot for obtaining
   * bitmap
   * 
   * @return
   */
  private boolean writeScreenshot() {

    // TODO this must write to external location

    FileOutputStream out = null;
    try {
      out = openFileOutput(createFileName() + ".png", MODE_WORLD_WRITEABLE);

      // bmp is your Bitmap instance
      Bitmap bmp = controller.screenShot();
      System.out.println("got bibimbap from controller");
      bmp.compress(Bitmap.CompressFormat.PNG, 100, out);
      System.out.println("done compressing bitmap and writing to file " + out.getFD());
      System.out.println("done writing to " + out);
    } catch (Exception e) {
      e.printStackTrace();
      return false;
    } finally {
      try {
        if (out != null) {
          out.close();
          System.out.println("File closed: " + out.getFD());
          System.out.println("File closed: " + out.toString());
        }
      } catch (IOException e) {
        e.printStackTrace();
        return false;
      }
    }
    return true;
  }

  public void delete() {
    final String[] files = fileList();

    AlertDialog.Builder builder = new AlertDialog.Builder(this);
    builder.setTitle("Delete file");
    builder.setItems(files, new DialogInterface.OnClickListener() {
      public void onClick(DialogInterface dialog, int item) {
        System.out.println("DELETE REQUEST " + item + " -- " + files[item]);

        if (deleteFile(files[item]))
          shortToast("Deleted file " + files[item]);
        else
          shortToast("Unable to delete file!");
      }
    });
    AlertDialog alert = builder.create();
    alert.show();
  }

  public void load() {
    System.out.println("load");
    final String[] files = fileList();

    AlertDialog.Builder builder = new AlertDialog.Builder(this);
    builder.setTitle("Pick a file");
    builder.setItems(files, new DialogInterface.OnClickListener() {
      public void onClick(DialogInterface dialog, int item) {
        Toast.makeText(getApplicationContext(), files[item], Toast.LENGTH_SHORT).show();
        try {
          StringBuffer stringBuffer = new StringBuffer();
          String inputLine = "";
          FileInputStream input = openFileInput(files[item].toString());
          InputStreamReader isr = new InputStreamReader(input);
          BufferedReader bufferedReader = new BufferedReader(isr);

          while ((inputLine = bufferedReader.readLine()) != null) {
            stringBuffer.append(inputLine);
            stringBuffer.append("\n");
          }

          bufferedReader.close();
          String json = stringBuffer.toString();
          System.out.println(json);

          new FileAccess().load(controller.getGraph(), json);

          controller.clearMemory();

          controller.makeInfo();
          controller.redraw();

        } catch (FileNotFoundException e) {
          // TODO Auto-generated catch block
          e.printStackTrace();
        } catch (IOException e) {
          // TODO Auto-generated catch block
          e.printStackTrace();
        } catch (JSONException e) {
          // TODO Auto-generated catch block
          e.printStackTrace();
        }
      }
    });
    AlertDialog alert = builder.create();
    alert.show();

  }

}
