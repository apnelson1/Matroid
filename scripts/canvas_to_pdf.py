#!/usr/bin/env python3
"""
Convert Obsidian canvas files to PDF.

This script reads .canvas files (JSON format) from the ToDo folder
and generates PDF visualizations showing the node layout and connections.
"""

import json
import sys
from pathlib import Path
from typing import Dict, List, Tuple

try:
    from reportlab.lib.pagesizes import A4, landscape
    from reportlab.lib.units import mm
    from reportlab.pdfgen import canvas as pdf_canvas
    from reportlab.lib import colors
    from reportlab.lib.utils import simpleSplit
except ImportError:
    print("Error: reportlab is required. Install it with: pip install reportlab")
    sys.exit(1)


# Color mapping for Obsidian canvas colors
COLOR_MAP = {
    "1": colors.HexColor("#e74c3c"),  # Red
    "2": colors.HexColor("#e67e22"),  # Orange
    "3": colors.HexColor("#f39c12"),  # Yellow
    "4": colors.HexColor("#2ecc71"),  # Green
    "5": colors.HexColor("#3498db"),  # Blue
    "6": colors.HexColor("#9b59b6"),  # Purple
}


def load_canvas(canvas_path: Path) -> Dict:
    """Load and parse a canvas JSON file."""
    with open(canvas_path, 'r', encoding='utf-8') as f:
        return json.load(f)


def get_canvas_bounds(nodes: List[Dict]) -> Tuple[float, float, float, float]:
    """Calculate the bounding box of all nodes."""
    if not nodes:
        return 0, 0, 800, 600
    
    min_x = min(node['x'] for node in nodes)
    max_x = max(node['x'] + node['width'] for node in nodes)
    min_y = min(node['y'] for node in nodes)
    max_y = max(node['y'] + node['height'] for node in nodes)
    
    # Add padding
    padding = 50
    return min_x - padding, min_y - padding, max_x + padding, max_y + padding


def transform_coords(x: float, y: float, canvas_bounds: Tuple[float, float, float, float],
                     pdf_width: float, pdf_height: float) -> Tuple[float, float]:
    """Transform canvas coordinates to PDF coordinates."""
    min_x, min_y, max_x, max_y = canvas_bounds
    canvas_width = max_x - min_x
    canvas_height = max_y - min_y
    
    # Calculate scale to fit on page
    scale_x = pdf_width / canvas_width
    scale_y = pdf_height / canvas_height
    scale = min(scale_x, scale_y) * 0.9  # 0.9 for some margin
    
    # Center the content
    offset_x = (pdf_width - canvas_width * scale) / 2
    offset_y = (pdf_height - canvas_height * scale) / 2
    
    # Transform coordinates (flip y-axis for PDF coordinates)
    pdf_x = (x - min_x) * scale + offset_x
    pdf_y = pdf_height - ((y - min_y) * scale + offset_y)
    
    return pdf_x, pdf_y


def get_node_color(node: Dict) -> colors.Color:
    """Get the color for a node."""
    color_id = node.get('color', '5')
    return COLOR_MAP.get(str(color_id), colors.HexColor("#3498db"))


def draw_node(c: pdf_canvas.Canvas, node: Dict, canvas_bounds: Tuple[float, float, float, float],
              pdf_width: float, pdf_height: float, scale: float):
    """Draw a single node on the PDF canvas."""
    x, y = node['x'], node['y']
    width, height = node['width'] * scale, node['height'] * scale
    
    # Transform coordinates
    pdf_x, pdf_y = transform_coords(x, y, canvas_bounds, pdf_width, pdf_height)
    pdf_y -= height  # Adjust for height
    
    # Get node color
    node_color = get_node_color(node)
    
    # Draw rectangle
    c.setStrokeColor(node_color)
    c.setFillColor(colors.HexColor("#ffffff"))
    c.setLineWidth(2)
    c.rect(pdf_x, pdf_y, width, height, stroke=1, fill=1)
    
    # Draw text
    if node.get('type') == 'file' and 'file' in node:
        file_name = Path(node['file']).stem  # Get filename without extension
        c.setFillColor(colors.black)
        c.setFont("Helvetica", 10)
        
        # Word wrap text to fit in box
        max_width = width - 10
        lines = simpleSplit(file_name, "Helvetica", 10, max_width)
        
        # Draw lines of text
        text_y = pdf_y + height - 15
        for line in lines[:int(height / 15)]:  # Limit lines to fit in height
            c.drawString(pdf_x + 5, text_y, line)
            text_y -= 12
    elif node.get('type') == 'text' and 'text' in node:
        text = node['text']
        c.setFillColor(colors.black)
        c.setFont("Helvetica", 10)
        
        # Word wrap text
        max_width = width - 10
        lines = simpleSplit(text, "Helvetica", 10, max_width)
        
        text_y = pdf_y + height - 15
        for line in lines[:int(height / 15)]:
            c.drawString(pdf_x + 5, text_y, line)
            text_y -= 12


def get_node_edge_point(node: Dict, side: str, canvas_bounds: Tuple[float, float, float, float],
                        pdf_width: float, pdf_height: float, scale: float) -> Tuple[float, float]:
    """Get the coordinates of an edge connection point on a node."""
    x, y = node['x'], node['y']
    width, height = node['width'], node['height']
    
    # Calculate center point for each side
    if side == 'top':
        edge_x, edge_y = x + width / 2, y
    elif side == 'bottom':
        edge_x, edge_y = x + width / 2, y + height
    elif side == 'left':
        edge_x, edge_y = x, y + height / 2
    elif side == 'right':
        edge_x, edge_y = x + width, y + height / 2
    else:  # default to center
        edge_x, edge_y = x + width / 2, y + height / 2
    
    # Transform to PDF coordinates
    pdf_x, pdf_y = transform_coords(edge_x, edge_y, canvas_bounds, pdf_width, pdf_height)
    return pdf_x, pdf_y


def draw_edge(c: pdf_canvas.Canvas, edge: Dict, nodes_dict: Dict[str, Dict],
              canvas_bounds: Tuple[float, float, float, float],
              pdf_width: float, pdf_height: float, scale: float):
    """Draw an edge between two nodes."""
    from_node_id = edge.get('fromNode')
    to_node_id = edge.get('toNode')
    
    if not from_node_id or not to_node_id:
        return
    
    from_node = nodes_dict.get(from_node_id)
    to_node = nodes_dict.get(to_node_id)
    
    if not from_node or not to_node:
        return
    
    from_side = edge.get('fromSide', 'right')
    to_side = edge.get('toSide', 'left')
    
    # Get edge points
    x1, y1 = get_node_edge_point(from_node, from_side, canvas_bounds, pdf_width, pdf_height, scale)
    x2, y2 = get_node_edge_point(to_node, to_side, canvas_bounds, pdf_width, pdf_height, scale)
    
    # Draw line with arrow
    c.setStrokeColor(colors.HexColor("#666666"))
    c.setLineWidth(1.5)
    c.line(x1, y1, x2, y2)
    
    # Draw arrowhead
    import math
    arrow_size = 8
    angle = math.atan2(y2 - y1, x2 - x1)
    
    # Calculate arrowhead points
    arrow_angle = math.pi / 6  # 30 degrees
    ax1 = x2 - arrow_size * math.cos(angle - arrow_angle)
    ay1 = y2 - arrow_size * math.sin(angle - arrow_angle)
    ax2 = x2 - arrow_size * math.cos(angle + arrow_angle)
    ay2 = y2 - arrow_size * math.sin(angle + arrow_angle)
    
    c.line(x2, y2, ax1, ay1)
    c.line(x2, y2, ax2, ay2)


def canvas_to_pdf(canvas_path: Path, output_path: Path):
    """Convert a canvas file to PDF."""
    print(f"Converting {canvas_path.name} to PDF...")
    
    # Load canvas data
    data = load_canvas(canvas_path)
    nodes = data.get('nodes', [])
    edges = data.get('edges', [])
    
    if not nodes:
        print(f"Warning: No nodes found in {canvas_path.name}")
        return
    
    # Calculate bounds
    canvas_bounds = get_canvas_bounds(nodes)
    min_x, min_y, max_x, max_y = canvas_bounds
    canvas_width = max_x - min_x
    canvas_height = max_y - min_y
    
    # Setup PDF
    pdf_width, pdf_height = landscape(A4)
    c = pdf_canvas.Canvas(str(output_path), pagesize=landscape(A4))
    
    # Calculate scale
    scale_x = pdf_width / canvas_width
    scale_y = pdf_height / canvas_height
    scale = min(scale_x, scale_y) * 0.9
    
    # Create nodes dictionary for edge lookup
    nodes_dict = {node['id']: node for node in nodes}
    
    # Draw title
    c.setFont("Helvetica-Bold", 16)
    c.setFillColor(colors.black)
    title = canvas_path.stem
    c.drawCentredString(pdf_width / 2, pdf_height - 20, title)
    
    # Draw edges first (so they appear behind nodes)
    for edge in edges:
        draw_edge(c, edge, nodes_dict, canvas_bounds, pdf_width, pdf_height, scale)
    
    # Draw nodes
    for node in nodes:
        draw_node(c, node, canvas_bounds, pdf_width, pdf_height, scale)
    
    # Save PDF
    c.save()
    print(f"✓ Created {output_path}")


def main():
    """Main entry point."""
    # Get script directory and project root
    script_dir = Path(__file__).parent
    project_root = script_dir.parent
    todo_dir = project_root / "ToDo"
    
    # Check if ToDo directory exists
    if not todo_dir.exists():
        print(f"Error: ToDo directory not found at {todo_dir}")
        sys.exit(1)
    
    # Find all canvas files
    canvas_files = list(todo_dir.glob("*.canvas"))
    
    if not canvas_files:
        print("No .canvas files found in ToDo directory")
        sys.exit(0)
    
    print(f"Found {len(canvas_files)} canvas file(s)")
    
    # Convert each canvas file
    for canvas_file in canvas_files:
        output_file = todo_dir / f"{canvas_file.stem}.pdf"
        try:
            canvas_to_pdf(canvas_file, output_file)
        except Exception as e:
            print(f"Error converting {canvas_file.name}: {e}")
            import traceback
            traceback.print_exc()
    
    print("\nDone!")


if __name__ == "__main__":
    main()
